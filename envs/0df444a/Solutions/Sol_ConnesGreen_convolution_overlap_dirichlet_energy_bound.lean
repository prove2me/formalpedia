-- Prove2me | solution 1 for ConnesGreen.convolution_overlap_dirichlet_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T19:14:53.74918+00:00
-- url     : https://prove2.me/submissions/4259a8f4-9432-47f6-96fa-5cd1643b001d

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

/-- Uniform overlap estimate in the original Dirichlet energy; the bound
vanishes linearly as the support overlap closes. -/
private theorem energy_overlap_bound (T : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest T g) (x : ℝ) :
    ‖conv g (starInv g) x‖ ≤ 2 * energy g * max (2 * T - |x|) 0 := by
  let a := max (-T) (x - T)
  let b := min T (x + T)
  have hsupport : ∀ s : ℝ, s ∉ Icc a b → g s * starRingEnd ℂ (g (-(x - s))) = 0 := by
    intro s hs
    by_cases hgs : g s = 0
    · simp [hgs]
    by_cases hgt : g (-(x - s)) = 0
    · simpa [neg_sub] using (show g s * starRingEnd ℂ (g (-(x - s))) = 0 by rw [hgt]; simp)
    have hs1 := hg.2 (subset_tsupport g hgs)
    have hs2 := hg.2 (subset_tsupport g hgt)
    apply False.elim
    apply hs
    exact ⟨max_le hs1.1.le (by linarith [hs2.1]), le_min hs1.2.le (by linarith [hs2.2])⟩
  have he : conv g (starInv g) x =
      ∫ s in Icc a b, g s * starRingEnd ℂ (g (-(x - s))) := by
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hsupport).symm
  have hb : ∀ s : ℝ, ‖g s * starRingEnd ℂ (g (-(x - s)))‖ ≤ 2 * energy g := by
    intro s
    have h1 := energy_point_bound T g hg s
    have h2 := energy_point_bound T g hg (-(x - s))
    have hn1 := norm_nonneg (g s)
    have hn2 := norm_nonneg (g (-(x - s)))
    have hp : ‖g s‖ * ‖g (-(x - s))‖ ≤ 2 * energy g := by
      nlinarith [sq_nonneg (‖g s‖ - ‖g (-(x - s))‖)]
    simpa only [norm_mul, RCLike.norm_conj] using hp
  have hm := norm_setIntegral_le_of_norm_le_const_ae
    (μ := volume) (f := fun s => g s * starRingEnd ℂ (g (-(x - s))))
    (s := Icc a b) (by simp [Real.volume_Icc]) (ae_of_all _ hb)
  have hlen : b - a = 2 * T - |x| := by
    dsimp [a, b]
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, max_eq_right (by linarith), min_eq_left (by linarith)]
      ring
    · rw [abs_of_neg (lt_of_not_ge hx), max_eq_left (by linarith), min_eq_right (by linarith)]
      ring
  rw [he]
  simpa only [Real.volume_real_Icc, hlen] using hm

theorem solution (T : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest T g) (x : ℝ) :
    ‖conv g (starInv g) x‖ ≤
      2 * ((∫ s : ℝ, ‖iteratedDeriv 1 g s‖ ^ 2) +
        (1 / 4 : ℝ) * (∫ s : ℝ, ‖g s‖ ^ 2)) * max (2 * T - |x|) 0 :=
  energy_overlap_bound T g hg x

