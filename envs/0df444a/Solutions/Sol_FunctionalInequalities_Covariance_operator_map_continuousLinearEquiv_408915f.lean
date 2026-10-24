-- Prove2me | solution 1 for FunctionalInequalities.Covariance.operator_map_continuousLinearEquiv_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:49:53.372613+00:00
-- url     : https://prove2.me/submissions/df26365e-588c-4b71-9169-69c70bda9e0c

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

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
universe u v
section LinearIsometry
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
variable (ν : ProbabilityMeasure V₁) (L : V₁ ≃ₗᵢ[ℝ] V₂)
variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] [SecondCountableTopology V₂]
/-- Without a finite second moment Mathlib's covariance operator is zero. -/
theorem FunctionalInequalities.Covariance.operator_of_not_memLp {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] (m : Measure W) (hm : ¬ MemLp id 2 m) : Covariance.operator m = 0 := by
  ext x
  apply ext_inner_right ℝ
  intro y
  rw [Covariance.operator_inner, ProbabilityTheory.covarianceBilin_of_not_memLp hm]
  simp
end LinearIsometry
section ContinuousLinearEquiv
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
variable (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] [SecondCountableTopology V₂]
namespace FunctionalInequalities.Covariance
end FunctionalInequalities.Covariance
open FunctionalInequalities.Covariance in
omit [SecondCountableTopology V₁] in
/-- Pushing a law forward along a continuous linear equivalence conjugates its covariance operator
by the map and its adjoint. Without a second moment both operators are zero. -/
theorem solution
    (ν : Measure V₁) [IsFiniteMeasure ν] (T : V₁ ≃L[ℝ] V₂) :
    FunctionalInequalities.Covariance.operator (ν.map T) =
      ((T : V₁ →L[ℝ] V₂).comp (FunctionalInequalities.Covariance.operator ν)).comp (T : V₁ →L[ℝ] V₂).adjoint := by
  have hcoe : ⇑(T : V₁ →L[ℝ] V₂) = ⇑T := rfl
  by_cases h : MemLp id 2 ν
  · ext u
    apply ext_inner_right ℝ
    intro v
    rw [FunctionalInequalities.Covariance.operator_inner, ← hcoe, ProbabilityTheory.covarianceBilin_map h (T : V₁ →L[ℝ] V₂),
      ← FunctionalInequalities.Covariance.operator_inner]
    simp only [ContinuousLinearMap.comp_apply]
    exact ContinuousLinearMap.adjoint_inner_right (T : V₁ →L[ℝ] V₂)
      (FunctionalInequalities.Covariance.operator ν ((T : V₁ →L[ℝ] V₂).adjoint u)) v
  · have h' : ¬ MemLp id 2 (ν.map T) := by
      intro h'
      apply h
      have h1 : MemLp (fun x ↦ T x) 2 ν :=
        (memLp_map_measure_iff aestronglyMeasurable_id T.continuous.measurable.aemeasurable).mp h'
      have h2 := (T.symm : V₂ →L[ℝ] V₁).comp_memLp' h1
      have h3 : (⇑(T.symm : V₂ →L[ℝ] V₁) ∘ fun x ↦ T x) = id := by
        funext x
        simp
      rwa [h3] at h2
    rw [FunctionalInequalities.Covariance.operator_of_not_memLp ν h, FunctionalInequalities.Covariance.operator_of_not_memLp (ν.map T) h']
    simp
