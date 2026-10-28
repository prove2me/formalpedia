-- Prove2me | solution 1 for FunctionalInequalities.Probability.affineSupport_mapContinuousLinearEquiv_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:38:47.856298+00:00
-- url     : https://prove2.me/submissions/c61824e7-fee0-47bc-bd08-77366e0f9f26

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport

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
open MeasureTheory Filter Topology InnerProductSpace
universe u v
section ContinuousLinearEquiv
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
variable (ν : MeasureTheory.ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] [SecondCountableTopology V₂]
variable [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
omit [CompleteSpace V₁] [CompleteSpace V₂] [FiniteDimensional ℝ V₁] in
/-- The affine support of the image law is the image of the affine support. -/
theorem solution :
    FunctionalInequalities.Probability.affineSupport (FunctionalInequalities.Probability.mapContinuousLinearEquiv ν T) = (FunctionalInequalities.Probability.affineSupport ν).map (T : V₁ →ₗ[ℝ] V₂).toAffineMap := by
  apply le_antisymm
  · apply FunctionalInequalities.Probability.affineSupport_le_of_ae_mem
    · exact ((FunctionalInequalities.Probability.affineSupport ν).map (T : V₁ →ₗ[ℝ] V₂).toAffineMap).closed_of_finiteDimensional
    · rw [FunctionalInequalities.Probability.coe_mapContinuousLinearEquiv]
      refine (ae_map_iff T.continuous.measurable.aemeasurable
        ((FunctionalInequalities.Probability.affineSupport ν).map
          (T : V₁ →ₗ[ℝ] V₂).toAffineMap).closed_of_finiteDimensional.measurableSet).2 ?_
      filter_upwards [FunctionalInequalities.Probability.ae_mem_affineSupport ν] with x hx
      exact ⟨x, hx, rfl⟩
  · rw [AffineSubspace.map_le_iff_le_comap]
    apply FunctionalInequalities.Probability.affineSupport_le_of_ae_mem
    · change IsClosed ((fun x : V₁ ↦ T x) ⁻¹' (FunctionalInequalities.Probability.affineSupport (FunctionalInequalities.Probability.mapContinuousLinearEquiv ν T) : Set V₂))
      exact (FunctionalInequalities.Probability.isClosed_affineSupport _).preimage T.continuous
    · have h := FunctionalInequalities.Probability.ae_mem_affineSupport (FunctionalInequalities.Probability.mapContinuousLinearEquiv ν T)
      rw [FunctionalInequalities.Probability.coe_mapContinuousLinearEquiv] at h
      filter_upwards [ae_of_ae_map T.continuous.measurable.aemeasurable h] with x hx
      exact hx
