-- Prove2me | solution 1 for FunctionalInequalities.Probability.affineSupport_intrinsicMeasure_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:49:51.007772+00:00
-- url     : https://prove2.me/submissions/f41486e5-efee-4d8e-876d-f339da97ae30

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support

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
section Coordinates
variable [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
omit [CompleteSpace E] in
/-- Intrinsic coordinates remove every redundant affine direction. This statement is purely
geometric and does not require log-concavity or absolute continuity. -/
theorem solution (μ : ProbabilityMeasure E) :
    FunctionalInequalities.Probability.affineSupport (FunctionalInequalities.Probability.intrinsicMeasure μ) = ⊤ := by
  let ν := FunctionalInequalities.Probability.intrinsicMeasure μ
  let A := (FunctionalInequalities.Probability.affineSupport ν).map (FunctionalInequalities.Probability.reconstruct μ).toAffineMap
  have hA : IsClosed (A : Set E) := A.closed_of_finiteDimensional
  have hfull : ∀ᵐ x ∂(μ : Measure E), x ∈ A := by
    rw [← (FunctionalInequalities.Probability.measurePreserving_reconstruct μ).map_eq]
    apply (ae_map_iff (FunctionalInequalities.Probability.measurable_reconstruct μ).aemeasurable hA.measurableSet).2
    filter_upwards [FunctionalInequalities.Probability.ae_mem_affineSupport ν] with v hv
    exact ⟨v, hv, rfl⟩
  have hle : FunctionalInequalities.Probability.affineSupport μ ≤ A := FunctionalInequalities.Probability.affineSupport_le_of_ae_mem μ A hA hfull
  apply top_unique
  intro v _
  have hv : FunctionalInequalities.Probability.reconstruct μ v ∈ FunctionalInequalities.Probability.affineSupport μ := (FunctionalInequalities.Probability.coordinateEquiv μ v).property
  obtain ⟨w, hw, heq⟩ := hle hv
  exact (FunctionalInequalities.Probability.reconstruct μ).injective heq ▸ hw
