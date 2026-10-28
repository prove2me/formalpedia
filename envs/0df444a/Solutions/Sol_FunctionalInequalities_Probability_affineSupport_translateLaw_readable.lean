-- Prove2me | solution 1 for FunctionalInequalities.Probability.affineSupport_translateLaw_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:40:11.332046+00:00
-- url     : https://prove2.me/submissions/1a7e2794-a2a2-432a-90f5-67659f24984d

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_IntrinsicTranslation

section
noncomputable section
open MeasureTheory
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]
/-- The affine support is the smallest closed affine subspace of full measure. -/
theorem FunctionalInequalities.Probability.affineSupport_le_of_ae_mem (μ : ProbabilityMeasure E) (A : AffineSubspace ℝ E)
    (hA : IsClosed (A : Set E)) (hμ : ∀ᵐ x ∂(μ : Measure E), x ∈ A) :
    affineSupport μ ≤ A := by
  apply affineSpan_le.mpr
  exact Measure.support_subset_of_isClosed hA hμ
end
end
end

noncomputable section
open MeasureTheory Filter Topology
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
variable (μ : MeasureTheory.ProbabilityMeasure E) (b : E)
/-- The affine support of the translated law is the translate of the affine support. -/
theorem solution :
    FunctionalInequalities.Probability.affineSupport (FunctionalInequalities.Probability.translateLaw μ b) =
      (FunctionalInequalities.Probability.affineSupport μ).map (AffineEquiv.constVAdd ℝ E b).toAffineMap := by
  apply le_antisymm
  · apply FunctionalInequalities.Probability.affineSupport_le_of_ae_mem
    · exact ((FunctionalInequalities.Probability.affineSupport μ).map (AffineEquiv.constVAdd ℝ E b).toAffineMap).closed_of_finiteDimensional
    · rw [FunctionalInequalities.Probability.coe_translateLaw]
      refine (ae_map_iff (measurable_const_add b).aemeasurable
        ((FunctionalInequalities.Probability.affineSupport μ).map
          (AffineEquiv.constVAdd ℝ E b).toAffineMap).closed_of_finiteDimensional.measurableSet).2 ?_
      filter_upwards [FunctionalInequalities.Probability.ae_mem_affineSupport μ] with x hx
      exact ⟨x, hx, rfl⟩
  · rw [AffineSubspace.map_le_iff_le_comap]
    apply FunctionalInequalities.Probability.affineSupport_le_of_ae_mem
    · change IsClosed ((fun x : E ↦ b + x) ⁻¹' (FunctionalInequalities.Probability.affineSupport (FunctionalInequalities.Probability.translateLaw μ b) : Set E))
      exact (FunctionalInequalities.Probability.isClosed_affineSupport _).preimage (continuous_const.add continuous_id)
    · have h := FunctionalInequalities.Probability.ae_mem_affineSupport (FunctionalInequalities.Probability.translateLaw μ b)
      rw [FunctionalInequalities.Probability.coe_translateLaw] at h
      filter_upwards [ae_of_ae_map (measurable_const_add b).aemeasurable h] with x hx
      exact hx
