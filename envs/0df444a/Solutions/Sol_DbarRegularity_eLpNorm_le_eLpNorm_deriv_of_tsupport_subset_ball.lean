-- Prove2me | solution 1 for DbarRegularity.eLpNorm_le_eLpNorm_deriv_of_tsupport_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T23:36:59.195436+00:00
-- url     : https://prove2.me/submissions/eef4639f-3a4c-43d7-9d98-615d7b805bbb

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp



namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal

/-- One-dimensional `L^p` Poincaré inequality: for real `p ≥ 1`, a `C¹` map `g : ℝ → E` with support
in `(-R, R)` satisfies `‖g‖_{L^p} ≤ 2R ‖g'‖_{L^p}`. -/
theorem eLpNorm_le_eLpNorm_deriv_of_tsupport_subset_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (R p : ℝ) (hp : 1 ≤ p) (g : ℝ → E) (hg : ContDiff ℝ 1 g)
    (hsupp : tsupport g ⊆ ball 0 R) :
    eLpNorm g (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (2 * R) * eLpNorm (deriv g) (ENNReal.ofReal p) volume := by
  have hzero : ∀ x, R ≤ |x| → g x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have := hsupp hm
    rw [mem_ball, Real.dist_eq, sub_zero] at this
    linarith
  have hdc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  rcases le_or_gt R 0 with hR | hR
  · have : g = 0 := funext fun x => hzero x (hR.trans (abs_nonneg x))
    simp [this]
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hPr : P.toReal = p := ENNReal.toReal_ofReal (by linarith)
  have hP1 : 1 ≤ P := ENNReal.one_le_ofReal.2 hp
  set μ := volume.restrict (Icc (-R) R) with hμ
  set a : ℝ≥0∞ := ENNReal.ofReal (2 * R) with ha
  have hμu : μ univ = a := by
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Icc]; congr 1; ring
  have ha0 : a ≠ 0 := by rw [ha]; simp; linarith
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  -- reduce to the interval
  have hsup : Function.support g ⊆ Icc (-R) R := by
    intro x hx
    by_contra h
    apply hx
    apply hzero
    by_contra h'
    push_neg at h'
    exact h ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  rw [← eLpNorm_restrict_eq_of_support_subset hsup]
  -- pointwise bound
  set J := ∫ x in Icc (-R) R, ‖deriv g x‖ with hJ
  have hpt : ∀ x, ‖g x‖ ≤ J := by
    intro x
    by_cases hx : R ≤ |x|
    · rw [hzero x hx, norm_zero]; exact setIntegral_nonneg measurableSet_Icc fun _ _ => norm_nonneg _
    push_neg at hx
    have hxl : -R ≤ x := by linarith [neg_abs_le x]
    have hxr : x ≤ R := by linarith [le_abs_self x]
    have hFTC : ∫ y in (-R)..x, deriv g y = g x - g (-R) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y _ => (hdiff y).hasDerivAt) (hdc.intervalIntegrable _ _)
    rw [hzero (-R) (by rw [abs_neg, abs_of_pos hR]), sub_zero] at hFTC
    rw [← hFTC]
    calc ‖∫ y in (-R)..x, deriv g y‖ ≤ ∫ y in (-R)..x, ‖deriv g y‖ :=
          intervalIntegral.norm_integral_le_integral_norm hxl
      _ = ∫ y in Ioc (-R) x, ‖deriv g y‖ := intervalIntegral.integral_of_le hxl
      _ ≤ J := by
          rw [hJ]
          apply setIntegral_mono_set (by fun_prop : Continuous fun y => ‖deriv g y‖).integrableOn_Icc
          · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
          · exact (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hxr)).eventuallyLE
  have h1 : eLpNorm g P μ ≤ μ univ ^ P.toReal⁻¹ * ENNReal.ofReal J :=
    eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall hpt)
  have h2 : ENNReal.ofReal J = eLpNorm (deriv g) 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm, hJ]
    exact ofReal_integral_norm_eq_lintegral_enorm hdc.integrableOn_Icc
  have h3 : eLpNorm (deriv g) 1 μ ≤ eLpNorm (deriv g) P μ * μ univ ^ (1 / (1 : ℝ≥0∞).toReal
      - 1 / P.toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ hP1 hdc.aestronglyMeasurable
  have h4 : eLpNorm (deriv g) P μ ≤ eLpNorm (deriv g) P volume :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  rw [hμu, hPr] at h1 h3
  calc eLpNorm g P μ ≤ a ^ p⁻¹ * ENNReal.ofReal J := h1
    _ ≤ a ^ p⁻¹ * (eLpNorm (deriv g) P volume * a ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p)) := by
        rw [h2]; gcongr; exact h3.trans (by gcongr)
    _ = a * eLpNorm (deriv g) P volume := by
        rw [mul_comm (eLpNorm _ _ _), ← mul_assoc, ← ENNReal.rpow_add _ _ ha0 hat]
        congr 1
        convert ENNReal.rpow_one a using 2
        simp

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (R p : ℝ) (hp : 1 ≤ p) (g : ℝ → E) (hg : ContDiff ℝ 1 g)
    (hsupp : tsupport g ⊆ ball 0 R) :
    eLpNorm g (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (2 * R) * eLpNorm (deriv g) (ENNReal.ofReal p) volume :=
  eLpNorm_le_eLpNorm_deriv_of_tsupport_subset_ball R p hp g hg hsupp
