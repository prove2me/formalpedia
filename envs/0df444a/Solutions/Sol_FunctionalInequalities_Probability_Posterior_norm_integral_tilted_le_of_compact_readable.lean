-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.norm_integral_tilted_le_of_compact_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:39.859972+00:00
-- url     : https://prove2.me/submissions/f6ad4d77-2d8c-4e3c-afe8-b43dbcd9432b

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]
/-- A tilted expectation of a statistic bounded on the support is bounded by the same constant. -/
theorem solution (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ f : Ω → ℝ}
    (hφ : Continuous φ) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    ‖∫ x, f x ∂((μ : Measure Ω).tilted φ)‖ ≤ C := by
  let : IsProbabilityMeasure ((μ : Measure Ω).tilted φ) := FunctionalInequalities.Probability.Posterior.isProbabilityMeasure_tilted_of_compact μ hc hφ
  have hi : Integrable f ((μ : Measure Ω).tilted φ) := by
    apply (integrable_tilted_iff (FunctionalInequalities.Probability.Posterior.integrable_exp_of_compact μ hc hφ) f).mpr
    simpa only [smul_eq_mul] using FunctionalInequalities.Probability.Posterior.integrable_exp_mul_of_compact μ hc hφ hf hC hb
  have hbound : ∀ᵐ x ∂((μ : Measure Ω).tilted φ), ‖f x‖ ≤ C := by
    apply (tilted_absolutelyContinuous (μ : Measure Ω) φ).ae_le
    filter_upwards [(μ : Measure Ω).support_mem_ae] with x hx
    exact hb x hx
  calc
    ‖∫ x, f x ∂((μ : Measure Ω).tilted φ)‖ ≤
        ∫ x, ‖f x‖ ∂((μ : Measure Ω).tilted φ) := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C ∂((μ : Measure Ω).tilted φ) := integral_mono_ae hi.norm (integrable_const C) hbound
    _ = C := by simp
