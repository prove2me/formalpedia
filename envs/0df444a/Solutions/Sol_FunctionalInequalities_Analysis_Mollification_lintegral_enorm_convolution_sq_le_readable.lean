-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Mollification.lintegral_enorm_convolution_sq_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:28:40.122204+00:00
-- url     : https://prove2.me/submissions/8b967e5f-9734-4b06-abe6-37f3f27cb1c5

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_enorm_convolution_sq_le_readable

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : MeasureTheory.Measure V} [m.IsAddHaarMeasure]
section Contraction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (φ : ContDiffBump (0 : V))
/-- The mollifier is an `L²` contraction: `∫ ‖ρ ⋆ f‖² ≤ ∫ ‖f‖²`. -/
theorem solution {f : V → E} (hf : AEStronglyMeasurable f m) :
    ∫⁻ x, ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ^ 2 ∂m ≤
      ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m := by
  have ha : Measurable fun t => ENNReal.ofReal (φ.normed m t) :=
    ENNReal.measurable_ofReal.comp φ.continuous_normed.measurable
  have hmeas : AEMeasurable (fun p : V × V => ENNReal.ofReal (φ.normed m p.2) *
      ‖f (p.1 - p.2)‖ₑ ^ 2) (m.prod m) := by
    refine (ha.comp measurable_snd).aemeasurable.mul ?_
    exact (hf.enorm.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant m m)).pow_const _
  have hint : ∫⁻ t, ENNReal.ofReal (φ.normed m t) ∂m = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
      (Filter.Eventually.of_forall φ.nonneg_normed), φ.integral_normed, ENNReal.ofReal_one]
  calc ∫⁻ x, ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ^ 2 ∂m
      ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (φ.normed m t) * ‖f (x - t)‖ₑ ^ 2 ∂m ∂m :=
        lintegral_mono fun x => FunctionalInequalities.Analysis.Mollification.enorm_convolution_sq_le_readable φ hf x
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (φ.normed m t) * ‖f (x - t)‖ₑ ^ 2 ∂m ∂m :=
        lintegral_lintegral_swap hmeas
    _ = ∫⁻ t, ENNReal.ofReal (φ.normed m t) * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m ∂m := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_sub_right_eq_self (fun x => ‖f x‖ₑ ^ 2) t]
    _ = (∫⁻ t, ENNReal.ofReal (φ.normed m t) ∂m) * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m :=
        lintegral_mul_const _ ha
    _ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m := by rw [hint, one_mul]
