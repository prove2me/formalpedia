-- Prove2me | solution 1 for FunctionalInequalities.Probability.affineSupport_mapContinuousLinearEquiv_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:37:09.629977+00:00
-- url     : https://prove2.me/submissions/56a7470e-88e3-48cd-a4bf-f4be58a8d786

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin

section
noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
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
end

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
universe u v
section ContinuousLinearEquiv
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
variable (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] [SecondCountableTopology V₂]
variable [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
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
