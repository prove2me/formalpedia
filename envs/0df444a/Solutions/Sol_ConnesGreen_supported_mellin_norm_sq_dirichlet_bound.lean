-- Prove2me | solution 1 for ConnesGreen.supported_mellin_norm_sq_dirichlet_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T19:35:36.936187+00:00
-- url     : https://prove2.me/submissions/b4580676-e3c9-464f-acba-1ccde6dfa6bf

import Definitions.Def_ConnesGreen_canonical_model
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier Set
open WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace
noncomputable section
private def energy (g : ℝ → ℂ) : ℝ :=
  (∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) + (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2)
private theorem energy_nonnegative (g : ℝ → ℂ) : 0 ≤ energy g := by
  exact add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
    (mul_nonneg (by norm_num) (integral_nonneg (fun _ => sq_nonneg _)))
private theorem energy_point_bound (T : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest T g) (x : ℝ) : ‖g x‖ ^ 2 ≤ 2 * energy g := by
  by_cases hx : g x = 0
  · simpa [hx] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (energy_nonnegative g)
  have hs := hg.2 (subset_tsupport g hx)
  have hcont : Continuous (deriv g) := by
    simpa only [iteratedDeriv_one] using hg.1.1.continuous_iteratedDeriv 1 (by simp)
  have hgd : HasCompactSupport (deriv g) := hg.1.2.deriv
  have hd : Integrable (fun s : ℝ => ‖deriv g s‖ ^ 2) := by
    apply (hcont.norm.pow 2).integrable_of_hasCompactSupport
    simpa only [pow_two, Pi.mul_apply] using
      (hgd.norm.mul_right (f' := fun s => ‖deriv g s‖))
  have hv : Integrable (fun s : ℝ => ‖g s‖ ^ 2) := by
    apply (hg.1.1.continuous.norm.pow 2).integrable_of_hasCompactSupport
    simpa only [pow_two, Pi.mul_apply] using
      (hg.1.2.norm.mul_right (f' := fun s => ‖g s‖))
  have hi := hd.add (hv.const_mul (1 / 4 : ℝ))
  have he : (∫ s : ℝ, ‖deriv g s‖ ^ 2 + (1 / 4 : ℝ) * ‖g s‖ ^ 2) = energy g := by
    rw [integral_add]
    · simp only [integral_const_mul, energy, iteratedDeriv_one]
    · exact hd
    · exact hv.const_mul _
  have hzero : g (-T) = 0 := (by
    by_contra hn
    have h := (hg.2 (subset_tsupport g hn)).1
    linarith)
  have hD : ∀ s : ℝ, HasDerivAt (fun s => ‖g s‖ ^ 2)
      (2 * inner ℝ (g s) (deriv g s)) s := by
    intro s
    exact (hg.1.1.differentiable (by norm_num) s).hasDerivAt.norm_sq
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hD s)
    (((hg.1.1.continuous.inner hcont).const_mul 2).intervalIntegrable (-T) x)
  have hb : ∀ s : ℝ, 2 * inner ℝ (g s) (deriv g s) ≤
      2 * (‖deriv g s‖ ^ 2 + (1 / 4 : ℝ) * ‖g s‖ ^ 2) := by
    intro s
    have hinner := real_inner_le_norm (g s) (deriv g s)
    nlinarith [sq_nonneg (‖deriv g s‖ - ‖g s‖ / 2)]
  have hm := intervalIntegral.integral_mono hs.1.le
    (((hg.1.1.continuous.inner hcont).const_mul 2).intervalIntegrable (-T) x)
    ((hi.const_mul 2).intervalIntegrable) hb
  have hn : 0 ≤ᵐ[volume] (fun s : ℝ => 2 * (‖deriv g s‖ ^ 2 + (1 / 4 : ℝ) * ‖g s‖ ^ 2)) :=
    ae_of_all _ (fun s => by positivity)
  have hglobal := setIntegral_le_integral (s := Ioc (-T) x) (hi.const_mul 2) hn
  simp only [intervalIntegral.integral_of_le hs.1.le] at hm hf
  rw [hf, hzero] at hm
  have hglobal' : (∫ s in Ioc (-T) x, 2 * (‖deriv g s‖ ^ 2 + (1 / 4 : ℝ) * ‖g s‖ ^ 2)) ≤
      2 * energy g := by
    calc
      _ ≤ ∫ s : ℝ, 2 * (‖deriv g s‖ ^ 2 + (1 / 4 : ℝ) * ‖g s‖ ^ 2) := hglobal
      _ = 2 * energy g := by rw [integral_const_mul, he]
  simpa using hm.trans hglobal'

private theorem mellin_energy_bound (T : ℝ) (hT : 0 ≤ T)
    (g : ℝ → ℂ) (hg : SupportedTest T g) (z : ℂ) :
    ‖mellinHat g z‖ ^ 2 ≤
      8 * T ^ 2 * Real.exp (2 * |z.re - 1 / 2| * T) * energy g := by
  let E := energy g
  have hE : 0 ≤ E := energy_nonnegative g
  have hsupport : ∀ s : ℝ, s ∉ Icc (-T) T →
      g s * Complex.exp ((z - 1 / 2) * s) = 0 := by
    intro s hs
    by_cases hgs : g s = 0
    · simp [hgs]
    have hm := hg.2 (subset_tsupport g hgs)
    exact False.elim (hs ⟨hm.1.le, hm.2.le⟩)
  have he : mellinHat g z = ∫ s in Icc (-T) T, g s * Complex.exp ((z - 1 / 2) * s) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hsupport).symm
  have hb : ∀ s : ℝ, ‖g s * Complex.exp ((z - 1 / 2) * s)‖ ≤
      Real.sqrt (2 * E) * Real.exp (|z.re - 1 / 2| * T) := by
    intro s
    by_cases hgs : g s = 0
    · simp only [hgs, zero_mul, norm_zero]
      positivity
    have hm := hg.2 (subset_tsupport g hgs)
    have hgn : ‖g s‖ ≤ Real.sqrt (2 * E) :=
      Real.le_sqrt_of_sq_le (energy_point_bound T g hg s)
    have hs : |s| ≤ T := abs_le.mpr ⟨hm.1.le, hm.2.le⟩
    have hx : ((z - 1 / 2) * (s : ℂ)).re ≤ |z.re - 1 / 2| * T := by
      simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      calc
        (z.re - 1 / 2) * s ≤ |(z.re - 1 / 2) * s| := le_abs_self _
        _ = |z.re - 1 / 2| * |s| := abs_mul _ _
        _ ≤ |z.re - 1 / 2| * T := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    rw [norm_mul, Complex.norm_exp]
    exact mul_le_mul hgn (Real.exp_le_exp.mpr hx) (by positivity) (by positivity)
  have hn := norm_setIntegral_le_of_norm_le_const_ae (μ := volume)
    (f := fun s : ℝ => g s * Complex.exp ((z - 1 / 2) * s))
    (s := Icc (-T) T) (by simp [Real.volume_Icc]) (ae_of_all _ hb)
  have hn' : ‖mellinHat g z‖ ≤
      (Real.sqrt (2 * E) * Real.exp (|z.re - 1 / 2| * T)) * (2 * T) := by
    rw [he]
    simpa only [Real.volume_real_Icc, sub_neg_eq_add, ← two_mul, max_eq_left (by positivity : (0 : ℝ) ≤ 2 * T)] using hn
  have hsquare : ‖mellinHat g z‖ ^ 2 ≤
      ((Real.sqrt (2 * E) * Real.exp (|z.re - 1 / 2| * T)) * (2 * T)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn' 2
  have hsqrt := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE)
  have hexp : Real.exp (|z.re - 1 / 2| * T) ^ 2 = Real.exp (2 * |z.re - 1 / 2| * T) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ _ := hsquare
    _ = _ := by simp only [mul_pow, hsqrt, hexp]; dsimp [E]; ring

theorem solution (T : ℝ) (hT : 0 ≤ T)
    (g : ℝ → ℂ) (hg : SupportedTest T g) (z : ℂ) :
    ‖mellinHat g z‖ ^ 2 ≤
      8 * T ^ 2 * Real.exp (2 * |z.re - 1 / 2| * T) *
        ((∫ s : ℝ, ‖iteratedDeriv 1 g s‖ ^ 2) +
          (1 / 4 : ℝ) * (∫ s : ℝ, ‖g s‖ ^ 2)) :=
  mellin_energy_bound T hT g hg z
