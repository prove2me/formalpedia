-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Mollification.enorm_convolution_sq_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:27:28.199996+00:00
-- url     : https://prove2.me/submissions/e3c6e368-95a2-4f67-971a-0854c3ce9461

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : MeasureTheory.Measure V} [m.IsAddHaarMeasure]
section Contraction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (φ : ContDiffBump (0 : V))
/-- Pointwise Cauchy–Schwarz for the mollifier: `‖(ρ ⋆ f) x‖² ≤ ∫ ρ(t) ‖f (x - t)‖² dt`. -/
theorem solution {f : V → E} (hf : AEStronglyMeasurable f m) (x : V) :
    ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ^ 2 ≤
      ∫⁻ t, ENNReal.ofReal (φ.normed m t) * ‖f (x - t)‖ₑ ^ 2 ∂m := by
  set a : V → ℝ≥0∞ := fun t => ENNReal.ofReal (φ.normed m t) with ha_def
  set b : V → ℝ≥0∞ := fun t => ‖f (x - t)‖ₑ with hb_def
  have ha : Measurable a := ENNReal.measurable_ofReal.comp φ.continuous_normed.measurable
  have hb : AEMeasurable b m :=
    hf.enorm.comp_quasiMeasurePreserving (Measure.measurePreserving_sub_left m x).quasiMeasurePreserving
  have h1 : ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ≤ ∫⁻ t, a t * b t ∂m := by
    rw [convolution_def]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun t => ?_
    simp only [ContinuousLinearMap.lsmul_apply, enorm_smul, Real.enorm_of_nonneg (φ.nonneg_normed t),
      ha_def, hb_def]
  have hint : ∫⁻ t, a t ∂m = 1 := by
    rw [ha_def, ← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
      (Filter.Eventually.of_forall φ.nonneg_normed), φ.integral_normed, ENNReal.ofReal_one]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq m Real.HolderConjugate.two_two
    (f := fun t => a t ^ (1 / 2 : ℝ)) (g := fun t => a t ^ (1 / 2 : ℝ) * b t)
    (ha.pow_const _).aemeasurable ((ha.pow_const _).aemeasurable.mul hb)
  have e1 : ∀ t, (a t ^ (1 / 2 : ℝ)) * (a t ^ (1 / 2 : ℝ) * b t) = a t * b t := by
    intro t
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ t, (a t ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a t := by
    intro t
    rw [← ENNReal.rpow_mul]; norm_num
  have e3 : ∀ t, (a t ^ (1 / 2 : ℝ) * b t) ^ (2 : ℝ) = a t * b t ^ 2 := by
    intro t
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ENNReal.rpow_two]
    norm_num
  simp only [Pi.mul_apply, e1, e2, e3, hint, ENNReal.one_rpow, one_mul] at hH
  have h2 : ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ≤
      (∫⁻ t, a t * b t ^ 2 ∂m) ^ (1 / (2 : ℝ)) := h1.trans hH
  calc ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ^ 2
      ≤ ((∫⁻ t, a t * b t ^ 2 ∂m) ^ (1 / (2 : ℝ))) ^ 2 := pow_le_pow_left' h2 2
    _ = ∫⁻ t, a t * b t ^ 2 ∂m := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
