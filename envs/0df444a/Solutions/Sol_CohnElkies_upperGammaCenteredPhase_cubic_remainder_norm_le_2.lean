-- Prove2me | solution 2 for CohnElkies.upperGammaCenteredPhase_cubic_remainder_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:46:54.785181+00:00
-- url     : https://prove2.me/submissions/2f397793-76c4-41f3-991b-3d92e9faf24a

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
theorem h47_uie_hasDerivAt (y : ℝ) :
    HasDerivAt CohnElkies.upperImaginaryExp (Complex.I * CohnElkies.upperImaginaryExp y) y := by
  have h1 : HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ)) (Complex.I * 1) y :=
    (hasDerivAt_id (y : ℂ)).comp_ofReal.const_mul Complex.I
  have := h1.cexp
  unfold CohnElkies.upperImaginaryExp
  convert this using 1
  ring
theorem h47_uie_iter (m : ℕ) : iteratedDeriv m CohnElkies.upperImaginaryExp =
    fun y => Complex.I ^ m * CohnElkies.upperImaginaryExp y := by
  have hD : deriv CohnElkies.upperImaginaryExp = fun y => Complex.I * CohnElkies.upperImaginaryExp y :=
    funext fun y => (h47_uie_hasDerivAt y).deriv
  induction m with
  | zero => funext y; simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    rw [deriv_const_mul _ (h47_uie_hasDerivAt y).differentiableAt, hD]
    ring
theorem h47_uie_norm (y : ℝ) : ‖CohnElkies.upperImaginaryExp y‖ = 1 := by
  unfold CohnElkies.upperImaginaryExp
  rw [Complex.norm_exp]
  simp
theorem h47_uie_contDiff : ContDiff ℝ ⊤ CohnElkies.upperImaginaryExp := by
  unfold CohnElkies.upperImaginaryExp
  exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

theorem h47c_iwd {x : ℝ} (hx : 0 < x) (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) x) :
    iteratedDerivWithin k CohnElkies.upperImaginaryExp (Set.Icc (0:ℝ) x) t =
      Complex.I ^ k * CohnElkies.upperImaginaryExp t := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
    (h47_uie_contDiff.contDiffAt.of_le (by exact_mod_cast le_top)) ht, h47_uie_iter]

theorem h47c_cubic_pos {x : ℝ} (hx : 0 < x) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1 - Complex.I * (x : ℂ) + ((x ^ 2 / 2 : ℝ) : ℂ)‖ ≤ x ^ 3 / 6 := by
  have hcd : ContDiffOn ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) CohnElkies.upperImaginaryExp (Set.uIcc 0 x) :=
    (h47_uie_contDiff.of_le (by exact_mod_cast le_top)).contDiffOn
  have hT := taylor_integral_remainder hcd
  rw [Set.uIcc_of_le hx.le] at hT
  have htay : taylorWithinEval CohnElkies.upperImaginaryExp 2 (Set.Icc (0 : ℝ) x) 0 x =
      1 + Complex.I * (x : ℂ) - ((x ^ 2 / 2 : ℝ) : ℂ) := by
    have hm : (0:ℝ) ∈ Set.Icc (0:ℝ) x := ⟨le_rfl, hx.le⟩
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, h47c_iwd hx _ hm]
    simp [CohnElkies.upperImaginaryExp]
    ring_nf
  rw [htay] at hT
  have hL : Complex.exp (Complex.I * (x : ℂ)) - 1 - Complex.I * (x : ℂ) + ((x ^ 2 / 2 : ℝ) : ℂ) =
      CohnElkies.upperImaginaryExp x - (1 + Complex.I * (x : ℂ) - ((x ^ 2 / 2 : ℝ) : ℂ)) := by
    unfold CohnElkies.upperImaginaryExp; ring
  rw [hL, hT]
  calc ‖∫ t in (0 : ℝ)..x, ((x - t) ^ 2 / (Nat.factorial 2 : ℝ)) •
          iteratedDerivWithin (2 + 1) CohnElkies.upperImaginaryExp (Set.Icc 0 x) t‖
      ≤ ∫ t in (0 : ℝ)..x, (x - t) ^ 2 / 2 := by
        apply intervalIntegral.norm_integral_le_of_norm_le hx.le
        · refine Filter.Eventually.of_forall fun t ht => ?_
          rw [norm_smul, h47c_iwd hx _ ⟨ht.1.le, ht.2⟩, norm_mul, norm_pow, Complex.norm_I, one_pow,
            one_mul, h47_uie_norm, mul_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          norm_num
        · apply Continuous.intervalIntegrable; fun_prop
    _ = x ^ 3 / 6 := by
        rw [intervalIntegral.integral_comp_sub_left (fun t => t ^ 2 / 2) x]
        simp only [sub_self, sub_zero]
        rw [intervalIntegral.integral_div, integral_pow]
        ring

theorem h47c_cubic (x : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1 - Complex.I * (x : ℂ) + ((x ^ 2 / 2 : ℝ) : ℂ)‖ ≤ |x| ^ 3 / 6 := by
  rcases lt_trichotomy x 0 with h | h | h
  · have := h47c_cubic_pos (neg_pos.mpr h)
    rw [abs_of_neg h]
    rw [← Complex.norm_conj] at this
    convert this using 2
    simp only [map_add, map_sub, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_conj]
    push_cast
    ring_nf
  · subst h; simp
  · rw [abs_of_pos h]; exact h47c_cubic_pos h

open CohnElkies in
theorem h47g_quad_int {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    IntegrableOn (upperGammaQuadraticKernel ℓ η T)
      (Ioi 0) := by
  have hmeas : Measurable (upperGammaQuadraticKernel ℓ η T) := by
    unfold upperGammaQuadraticKernel upperGammaMeasureDensity; fun_prop
  have hg : IntegrableOn (fun a : ℝ => T ^ 2 / 2 * ((ℓ / 2) * Real.exp (-η * a) + a * Real.exp (-η * a))) (Ioi 0) := by
    apply Integrable.const_mul
    apply Integrable.add
    · exact (exp_neg_integrableOn_Ioi 0 hη).const_mul _
    · have := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := η) (by norm_num) one_pos hη)
      refine this.congr_fun (fun a ha => ?_) measurableSet_Ioi
      simp only [Real.rpow_one]
  refine Integrable.mono' hg hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  have ha' : (0:ℝ) < a := ha
  unfold upperGammaQuadraticKernel upperGammaMeasureDensity
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hx : 0 < 2 * a / ℓ := by positivity
  have hE : Real.exp (-(2 * a / ℓ)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by linarith
  -- 1 - e^{-x} ≥ x/(1+x)
  have hbound : (2 * a / ℓ) / (1 + 2 * a / ℓ) ≤ 1 - Real.exp (-(2 * a / ℓ)) := by
    have h1 := Real.add_one_le_exp (2 * a / ℓ)
    have h2 : Real.exp (-(2 * a / ℓ)) = (Real.exp (2 * a / ℓ))⁻¹ := Real.exp_neg _
    rw [h2, div_le_iff₀ (by positivity)]
    have h3 := Real.exp_pos (2 * a / ℓ)
    have h4 : (Real.exp (2 * a / ℓ))⁻¹ * Real.exp (2 * a / ℓ) = 1 := inv_mul_cancel₀ h3.ne'
    nlinarith [mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr h3.le)]
  have he := Real.exp_pos (-η * a)
  rw [abs_of_nonneg (by positivity)]
  have key : a / (1 - Real.exp (-(2 * a / ℓ))) ≤ ℓ / 2 + a := by
    rw [div_le_iff₀ hden]
    have : (ℓ / 2 + a) * ((2 * a / ℓ) / (1 + 2 * a / ℓ)) = a := by field_simp <;> ring
    nlinarith [mul_le_mul_of_nonneg_left hbound (by positivity : (0:ℝ) ≤ ℓ / 2 + a)]
  calc (a * T) ^ 2 / 2 * (Real.exp (-η * a) / (a * (1 - Real.exp (-(2 * a / ℓ)))))
      = T ^ 2 / 2 * Real.exp (-η * a) * (a / (1 - Real.exp (-(2 * a / ℓ)))) := by
        field_simp
    _ ≤ T ^ 2 / 2 * Real.exp (-η * a) * (ℓ / 2 + a) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = T ^ 2 / 2 * ((ℓ / 2) * Real.exp (-η * a) + a * Real.exp (-η * a)) := by ring

open CohnElkies in
theorem h47g_third_int {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) :
    IntegrableOn
      (fun a : ℝ => a ^ 3 * upperGammaMeasureDensity ℓ η a)
      (Set.Ioi 0) := by
  have hI : ∀ s : ℝ, -1 < s → IntegrableOn (fun x : ℝ => x ^ s * Real.exp (-η * x)) (Ioi 0) := by
    intro s hs
    have := integrableOn_rpow_mul_exp_neg_mul_rpow hs one_pos hη
    simpa [Real.rpow_one] using this
  have hmaj : IntegrableOn (fun a : ℝ => a ^ (2:ℝ) * Real.exp (-η * a) +
      (ℓ / 2) * (a ^ (1:ℝ) * Real.exp (-η * a))) (Ioi 0) :=
    (hI 2 (by norm_num)).add ((hI 1 (by norm_num)).const_mul _)
  have hden : ∀ a : ℝ, 0 < a → 0 < 1 - Real.exp (-(2 * a / ℓ)) := by
    intro a ha
    have : Real.exp (-(2 * a / ℓ)) < 1 :=
      Real.exp_lt_one_iff.2 (by have := div_pos (by linarith : 0 < 2*a) hℓ; linarith)
    linarith
  refine hmaj.mono' ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    unfold upperGammaMeasureDensity
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro a ha
    exact mul_ne_zero (ne_of_gt ha) (hden a ha).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have ha0 : 0 < a := ha
    have hd := hden a ha0
    have he := Real.exp_pos (-η * a)
    unfold upperGammaMeasureDensity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_two, Real.rpow_one]
    set y := 2 * a / ℓ with hy
    have hy0 : 0 < y := by positivity
    have hq : Real.exp (-y) * (1 + y) ≤ 1 := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos y)]
      linarith [Real.add_one_le_exp y]
    rw [show a ^ 3 * (Real.exp (-η * a) / (a * (1 - Real.exp (-y)))) =
        a ^ 2 * Real.exp (-η * a) / (1 - Real.exp (-y)) by field_simp]
    rw [div_le_iff₀ hd]
    have hyl : y * ℓ = 2 * a := by rw [hy]; field_simp
    have h1 : 0 ≤ a * Real.exp (-η * a) * ℓ / 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hq h1
    have hay : a = y * ℓ / 2 := by linarith
    have h3 : a * (a * Real.exp (-η * a)) = y * ℓ / 2 * (a * Real.exp (-η * a)) := by rw [← hay]
    have h4 : a * (a * Real.exp (-η * a)) * Real.exp (-y) =
        y * ℓ / 2 * (a * Real.exp (-η * a)) * Real.exp (-y) := by rw [← hay]
    nlinarith [h2, h3, h4]

open CohnElkies in
theorem h47g_quad_eq {ℓ η : ℝ} (hℓ : 0 < ℓ)
    (T : ℝ) :
    (∫ a : ℝ in Ioi 0,
      upperGammaQuadraticKernel ℓ η T a) =
        ((ℓ * upperGammaVariance ℓ η / 2 * T ^ 2 : ℝ) : ℂ) := by
  unfold upperGammaQuadraticKernel upperGammaVariance
  rw [integral_complex_ofReal]
  congr 1
  rw [show (fun a : ℝ => (a * T) ^ 2 / 2 * upperGammaMeasureDensity ℓ η a) =
      fun a : ℝ => (T ^ 2 / 2) * (a ^ 2 * upperGammaMeasureDensity ℓ η a) by
    funext a; ring, integral_const_mul]
  field_simp

theorem solution
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    ‖upperGammaCenteredPhase ℓ η T +
        ((ℓ * upperGammaVariance ℓ η / 2 * T ^ 2 : ℝ) : ℂ)‖ ≤
      (ℓ * upperGammaThirdMoment ℓ η / 6) * |T| ^ 3 := by
  have hden : ∀ a : ℝ, 0 < a → 0 < upperGammaMeasureDensity ℓ η a := by
    intro a ha
    unfold upperGammaMeasureDensity
    apply div_pos (Real.exp_pos _)
    apply mul_pos ha
    have : Real.exp (-(2 * a / ℓ)) < 1 := Real.exp_lt_one_iff.mpr (by have := div_pos (mul_pos two_pos ha) hℓ; linarith)
    linarith
  have hbound : ∀ a : ℝ, 0 < a → ‖upperGammaCubicRemainderKernel ℓ η T a‖ ≤
      (|T| ^ 3 / 6) * (a ^ 3 * upperGammaMeasureDensity ℓ η a) := by
    intro a ha
    unfold upperGammaCubicRemainderKernel upperImaginaryExp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hden a ha).le]
    have := h47c_cubic (a * T)
    have hd0 := (hden a ha).le
    calc _ ≤ |a * T| ^ 3 / 6 * upperGammaMeasureDensity ℓ η a := by gcongr
      _ = _ := by rw [abs_mul, abs_of_pos ha]; ring
  have hcub_int : IntegrableOn (upperGammaCubicRemainderKernel ℓ η T) (Ioi 0) := by
    refine ((h47g_third_int hℓ hη).const_mul (|T| ^ 3 / 6)).mono' ?_ ?_
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro a ha
      have ha' : (0:ℝ) < a := ha
      apply ContinuousAt.continuousWithinAt
      have hc : ContinuousAt (upperGammaMeasureDensity ℓ η) a := by
        unfold upperGammaMeasureDensity
        apply ContinuousAt.div (by fun_prop) (by fun_prop)
        have := hden a ha'
        unfold upperGammaMeasureDensity at this
        intro h0; rw [h0, div_zero] at this; exact lt_irrefl _ this
      unfold upperGammaCubicRemainderKernel upperImaginaryExp
      have hc' : ContinuousAt (fun a => (upperGammaMeasureDensity ℓ η a : ℂ)) a :=
        Complex.continuous_ofReal.continuousAt.comp hc
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      exact hbound a ha
  have hsplit : ∀ a : ℝ, upperGammaCenteredKernel ℓ η T a =
      upperGammaCubicRemainderKernel ℓ η T a - upperGammaQuadraticKernel ℓ η T a := by
    intro a
    unfold upperGammaCenteredKernel upperGammaCubicRemainderKernel upperGammaQuadraticKernel
    push_cast; ring
  have hphase : upperGammaCenteredPhase ℓ η T =
      (∫ a in Ioi 0, upperGammaCubicRemainderKernel ℓ η T a) -
        ((ℓ * upperGammaVariance ℓ η / 2 * T ^ 2 : ℝ) : ℂ) := by
    unfold upperGammaCenteredPhase
    simp_rw [hsplit]
    rw [integral_sub hcub_int (h47g_quad_int hℓ hη T), h47g_quad_eq hℓ T]
  rw [hphase, sub_add_cancel]
  calc ‖∫ a in Ioi 0, upperGammaCubicRemainderKernel ℓ η T a‖
      ≤ ∫ a in Ioi 0, (|T| ^ 3 / 6) * (a ^ 3 * upperGammaMeasureDensity ℓ η a) := by
        apply norm_integral_le_of_norm_le ((h47g_third_int hℓ hη).const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
        exact hbound a ha
    _ = (ℓ * upperGammaThirdMoment ℓ η / 6) * |T| ^ 3 := by
        rw [integral_const_mul]
        unfold upperGammaThirdMoment
        field_simp

