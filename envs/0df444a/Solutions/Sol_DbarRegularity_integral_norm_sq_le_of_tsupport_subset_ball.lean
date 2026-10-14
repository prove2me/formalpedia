-- Prove2me | solution 1 for DbarRegularity.integral_norm_sq_le_of_tsupport_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T23:01:58.766528+00:00
-- url     : https://prove2.me/submissions/ce42a40c-3dde-42b6-b8f1-b8cf9d8208b6

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real



namespace DbarRegularity

open MeasureTheory Metric Set

/-- One-dimensional L² Poincaré inequality: a `C¹` map `g : ℝ → E` with support in `(-R, R)`
satisfies `∫ ‖g‖² ≤ 4R² ∫ ‖g'‖²`. -/
theorem integral_norm_sq_le_of_tsupport_subset_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (R : ℝ) (g : ℝ → E) (hg : ContDiff ℝ 1 g)
    (hsupp : tsupport g ⊆ ball 0 R) :
    ∫ x, ‖g x‖ ^ 2 ≤ 4 * R ^ 2 * ∫ x, ‖deriv g x‖ ^ 2 := by
  have hzero : ∀ x, R ≤ |x| → g x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have := hsupp hm
    rw [mem_ball, Real.dist_eq, sub_zero] at this
    linarith
  have hdc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hgc : Continuous g := hg.continuous
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hdzero : ∀ x, R ≤ |x| → deriv g x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have := hsupp (tsupport_deriv_subset hm)
    rw [mem_ball, Real.dist_eq, sub_zero] at this
    linarith
  set I := ∫ x, ‖deriv g x‖ ^ 2 with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => by positivity
  rcases le_or_gt R 0 with hR | hR
  · have : ∀ x, g x = 0 := fun x => hzero x (hR.trans (abs_nonneg x))
    simp only [this, norm_zero]
    have : (0:ℝ) ^ 2 = 0 := by norm_num
    simp only [this, integral_zero]
    positivity
  -- integrability of the derivative terms on the interval
  have hsq_int : Integrable (fun x => ‖deriv g x‖ ^ 2) := by
    have hcs : HasCompactSupport (fun x => ‖deriv g x‖ ^ 2) := by
      apply HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R))
      intro x hx
      have : R ≤ |x| := by
        by_contra h
        push_neg at h
        exact hx ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
      simp [hdzero x this]
    exact (by fun_prop : Continuous fun x => ‖deriv g x‖ ^ 2).integrable_of_hasCompactSupport hcs
  -- Cauchy–Schwarz on [-R, R]
  set J := ∫ x in Icc (-R) R, ‖deriv g x‖ with hJ
  have hCS : J ^ 2 ≤ 2 * R * ∫ x in Icc (-R) R, ‖deriv g x‖ ^ 2 := by
    set f : ℝ → ℝ := fun x => ‖deriv g x‖
    have hfc : Continuous f := by fun_prop
    have hvol : volume.real (Icc (-R) R) = 2 * R := by
      rw [Real.volume_real_Icc_of_le (by linarith)]; ring
    set c := J / (2 * R)
    have hf1 : IntegrableOn f (Icc (-R) R) := hfc.integrableOn_Icc
    have hf2 : IntegrableOn (fun x => f x ^ 2) (Icc (-R) R) := (hfc.pow 2).integrableOn_Icc
    have hc1 : IntegrableOn (fun _ : ℝ => c ^ 2) (Icc (-R) R) := continuous_const.integrableOn_Icc
    have hcf : IntegrableOn (fun x => 2 * c * f x) (Icc (-R) R) := hf1.const_mul _
    have h0 : 0 ≤ ∫ x in Icc (-R) R, (f x - c) ^ 2 := setIntegral_nonneg measurableSet_Icc
      fun _ _ => sq_nonneg _
    have hexp : ∫ x in Icc (-R) R, (f x - c) ^ 2
        = (∫ x in Icc (-R) R, f x ^ 2) - 2 * c * J + c ^ 2 * (2 * R) := by
      have : (fun x => (f x - c) ^ 2) = fun x => (f x ^ 2 - 2 * c * f x) + c ^ 2 := by
        funext x; ring
      rw [this, integral_add, integral_sub, integral_const_mul,
        setIntegral_const, hvol, smul_eq_mul]
      all_goals first | exact hf2 | exact hcf | exact hc1 | exact hf2.sub hcf | ring
    rw [hexp] at h0
    have h2R : 0 < 2 * R := by linarith
    have : c ^ 2 * (2 * R) = J * c := by simp only [c]; field_simp
    have : 2 * c * J = 2 * (J * c) := by ring
    have hJc : J * c * (2 * R) = J ^ 2 := by simp only [c]; field_simp
    nlinarith
  -- pointwise bound
  have hpt : ∀ x, ‖g x‖ ^ 2 ≤ 2 * R * I := by
    intro x
    by_cases hx : R ≤ |x|
    · rw [hzero x hx, norm_zero]; norm_num; positivity
    push_neg at hx
    have hxl : -R ≤ x := by linarith [neg_abs_le x]
    have hxr : x ≤ R := by linarith [le_abs_self x]
    have hFTC : ∫ y in (-R)..x, deriv g y = g x - g (-R) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y _ => (hdiff y).hasDerivAt) (hdc.intervalIntegrable _ _)
    rw [hzero (-R) (by rw [abs_neg, abs_of_pos hR]), sub_zero] at hFTC
    have h1 : ‖g x‖ ≤ J := by
      rw [← hFTC]
      calc ‖∫ y in (-R)..x, deriv g y‖ ≤ ∫ y in (-R)..x, ‖deriv g y‖ :=
            intervalIntegral.norm_integral_le_integral_norm hxl
        _ = ∫ y in Ioc (-R) x, ‖deriv g y‖ := intervalIntegral.integral_of_le hxl
        _ ≤ J := by
          rw [hJ]
          apply setIntegral_mono_set (by fun_prop : Continuous fun y => ‖deriv g y‖).integrableOn_Icc
          · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
          · exact (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hxr)).eventuallyLE
    have h2 : ∫ x in Icc (-R) R, ‖deriv g x‖ ^ 2 ≤ I :=
      setIntegral_le_integral hsq_int (Filter.Eventually.of_forall fun _ => by positivity)
    calc ‖g x‖ ^ 2 ≤ J ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ 2 * R * ∫ x in Icc (-R) R, ‖deriv g x‖ ^ 2 := hCS
      _ ≤ 2 * R * I := by gcongr
  -- integrate
  have hrestrict : ∫ x, ‖g x‖ ^ 2 = ∫ x in Icc (-R) R, ‖g x‖ ^ 2 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    have : R ≤ |x| := by
      by_contra h
      push_neg at h
      exact hx ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    simp [hzero x this]
  rw [hrestrict]
  calc ∫ x in Icc (-R) R, ‖g x‖ ^ 2 ≤ ∫ x in Icc (-R) R, 2 * R * I := by
        apply setIntegral_mono_on (by fun_prop : Continuous fun x => ‖g x‖ ^ 2).integrableOn_Icc
          continuous_const.integrableOn_Icc measurableSet_Icc
        intro x _; exact hpt x
    _ = 4 * R ^ 2 * I := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]; ring

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Set

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (R : ℝ) (g : ℝ → E) (hg : ContDiff ℝ 1 g)
    (hsupp : tsupport g ⊆ ball 0 R) :
    ∫ x, ‖g x‖ ^ 2 ≤ 4 * R ^ 2 * ∫ x, ‖deriv g x‖ ^ 2 :=
  integral_norm_sq_le_of_tsupport_subset_ball R g hg hsupp
