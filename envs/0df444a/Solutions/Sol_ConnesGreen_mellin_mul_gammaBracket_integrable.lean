-- Prove2me | solution 1 for ConnesGreen.mellin_mul_gammaBracket_integrable
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T03:25:51.473974+00:00
-- url     : https://prove2.me/submissions/1150f10b-eb6b-4904-a8be-cc65698a8024

import Definitions.Def_ConnesRZ_weil_defs
import Theorems.Thm_Zeta23_WeilEF_digamma_growth_strip
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Complex MeasureTheory ConnesRZ
open scoped FourierTransform
noncomputable section
private theorem mellin_fourier_dictionary (g : ℝ → ℂ) (r : ℝ) :
    mellinHat g (1 / 2 + I * r) = 𝓕 g (-r / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold mellinHat
  simp only [add_sub_cancel_left]
  congr 1
  ext u
  rw [smul_eq_mul, mul_comm (g u)]
  congr 1
  have h : (-2 * Real.pi * u * (-r / (2 * Real.pi))) = r * u := by field_simp
  rw [h]
  push_cast
  ring

private theorem digamma_right_differentiable : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ Complex.digamma s := by
  intro s hs
  have hzero : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m h
    rw [h] at hs
    simp only [Complex.neg_re, Complex.natCast_re] at hs
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΓan : AnalyticAt ℂ Complex.Gamma s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hopen.mem_nhds hs] with w hw
    refine Complex.differentiableAt_Gamma w fun m => ?_
    intro h
    rw [h] at hw
    simp only [Complex.neg_re, Complex.natCast_re] at hw
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hΓne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hzero
  have hψan : AnalyticAt ℂ Complex.digamma s := by
    have h1 : AnalyticAt ℂ (deriv Complex.Gamma) s := hΓan.deriv
    have h2 := h1.div hΓan hΓne
    exact h2.congr (by
      filter_upwards with w
      rw [Complex.digamma_def, logDeriv_apply]
      rfl)
  exact hψan.differentiableAt
theorem solution (k : ℝ → ℂ) (hk : IsTest k) :
    Integrable (fun r : ℝ => mellinHat k (1 / 2 + I * r) *
      (((Complex.digamma (1 / 4 + I * r / 2)).re - Real.log Real.pi : ℝ) : ℂ)) := by 
  let f := hk.2.toSchwartzMap (hk.1.of_le (by simp))
  let F := (𝓕 f : SchwartzMap ℝ ℂ)
  let a : ℝ := -(1 / (2 * Real.pi))
  have ha : a ≠ 0 := neg_ne_zero.mpr (div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have he : ∀ r : ℝ, mellinHat k (1 / 2 + I * r) = F (a*r) := by
    intro r
    rw [mellin_fourier_dictionary]
    change 𝓕 k (-r / (2 * Real.pi)) = 𝓕 k (a*r)
    congr 1
    dsimp [a]
    ring
  have h0 : Integrable (fun r : ℝ => ‖mellinHat k (1 / 2 + I*r)‖) := by
    simpa only [he] using F.integrable.norm.comp_mul_left' ha
  have h1 : Integrable (fun r : ℝ => ‖r‖ * ‖mellinHat k (1 / 2 + I*r)‖) := by
    have h := (F.integrable_pow_mul volume 1).comp_mul_left' ha
    have h := h.const_mul (1 / ‖a‖)
    apply h.congr
    filter_upwards [] with r
    simp only [pow_one, norm_mul, he]
    field_simp [norm_ne_zero_iff.mpr ha]
  obtain ⟨C, hC, hbound⟩ := Zeta23.WeilEF.digamma_growth_strip
  let D := 2*C + |Real.log Real.pi|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hγ : ∀ r : ℝ, |(Complex.digamma (1/4 + I*r/2)).re - Real.log Real.pi| ≤ D*(1+‖r‖) := by
    intro r
    have hb := hbound (1/4 + I*r/2) (by simp) (by norm_num)
    have hi : |(1/4 + I*(r:ℂ)/2 : ℂ).im| = |r|/2 := by simp [abs_div]
    rw [hi] at hb
    have hl := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 2+|r|/2)
    have hsub := abs_sub (Complex.digamma (1/4+I*r/2)).re (Real.log Real.pi)
    have hr := Complex.abs_re_le_norm (Complex.digamma (1/4+I*r/2))
    rw [Real.norm_eq_abs]
    dsimp [D]
    nlinarith [abs_nonneg r, abs_nonneg (Real.log Real.pi)]
  have hcont : Continuous (fun r : ℝ => (Complex.digamma (1/4 + I*r/2)).re - Real.log Real.pi) := by
    apply Continuous.sub _ continuous_const
    apply Complex.continuous_re.comp
    rw [continuous_iff_continuousAt]
    intro r
    apply (digamma_right_differentiable _ (by simp)).continuousAt.comp
    fun_prop
  have hkcont : Continuous (fun r : ℝ => mellinHat k (1/2 + I*r)) := by
    have hc : Continuous (fun r : ℝ => F (a*r)) :=
      F.continuous.comp (continuous_const.mul continuous_id)
    simpa only [he] using hc
  have hmaj := (h0.add h1).const_mul D
  apply hmaj.mono' ((hkcont.mul (Complex.continuous_ofReal.comp hcont)).aestronglyMeasurable)
  filter_upwards [] with r
  simp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_left (hγ r) (norm_nonneg (mellinHat k (1/2+I*r)))
  rw [Real.norm_eq_abs] at h
  dsimp at ⊢
  nlinarith
