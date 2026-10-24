-- Prove2me | solution 1 for FunctionalInequalities.Covariance.bilin_intrinsic_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:49:11.410843+00:00
-- url     : https://prove2.me/submissions/537b3106-542e-4e03-b9cb-95487d701d3a

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
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
section Coordinates
variable [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
omit [CompleteSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- On the affine support, the retraction is the identity. -/
@[simp]
theorem FunctionalInequalities.Probability.coe_retraction_of_mem (μ : ProbabilityMeasure E) {x : E}
    (hx : x ∈ affineSupport μ) : (retraction μ x : E) = x := by
  classical
  simp [retraction, hx]
end Coordinates
end
end
end
end

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable [SecondCountableTopology E] [FiniteDimensional ℝ E]
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
omit [CompleteSpace E] [BorelSpace E] in
/-- Intrinsic coordinates are, almost everywhere, the orthogonal projection of the displacement
from the chosen support point onto the direction space. -/
theorem FunctionalInequalities.Probability.intrinsicMap_ae_eq_orthogonalProjection (μ : ProbabilityMeasure E) :
    intrinsicMap μ =ᵐ[(μ : Measure E)]
      fun x ↦ (affineSupport μ).direction.orthogonalProjectionOnto (x - supportPoint μ) := by
  filter_upwards [ae_mem_affineSupport μ] with x hx
  have hdir : x - supportPoint μ ∈ (affineSupport μ).direction :=
    AffineSubspace.vsub_mem_direction hx (origin μ).property
  have hret : retraction μ x = ⟨x, hx⟩ := Subtype.ext (coe_retraction_of_mem μ hx)
  rw [intrinsicMap, hret, coordinateEquiv, AffineIsometryEquiv.coe_vaddConst_symm]
  apply Subtype.ext
  rw [← Submodule.starProjection_apply, Submodule.starProjection_eq_self_iff.mpr hdir]
  rfl
end
end
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Covariance
end FunctionalInequalities.Covariance
open FunctionalInequalities FunctionalInequalities.Covariance
open Probability
namespace FunctionalInequalities.Covariance
end FunctionalInequalities.Covariance
open FunctionalInequalities.Covariance in
/-- The ambient covariance bilinear form restricted to the direction space is the covariance
bilinear form of the intrinsic law. -/
theorem solution (μ : ProbabilityMeasure E) (hμ : MemLp id 2 (μ : Measure E))
    (v w : (FunctionalInequalities.Probability.affineSupport μ).direction) :
    covarianceBilin (FunctionalInequalities.Probability.intrinsicMeasure μ : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) v w =
      covarianceBilin (μ : Measure E) v w := by
  set P := (FunctionalInequalities.Probability.affineSupport μ).direction.orthogonalProjectionOnto
  have hshift : Measurable fun x : E ↦ -FunctionalInequalities.Probability.supportPoint μ + x := by fun_prop
  have hmap : (FunctionalInequalities.Probability.intrinsicMeasure μ : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) =
      ((μ : Measure E).map (fun x ↦ -FunctionalInequalities.Probability.supportPoint μ + x)).map P := by
    rw [FunctionalInequalities.Probability.intrinsicMeasure, ProbabilityMeasure.toMeasure_map,
      Measure.map_map P.continuous.measurable hshift]
    refine Measure.map_congr ?_
    filter_upwards [FunctionalInequalities.Probability.intrinsicMap_ae_eq_orthogonalProjection μ] with x hx
    rw [hx, Function.comp_apply, sub_eq_neg_add]
  have hμ' : MemLp id 2 ((μ : Measure E).map fun x ↦ -FunctionalInequalities.Probability.supportPoint μ + x) :=
    (measurableEmbedding_addLeft _).memLp_map_measure_iff.mpr
      ((memLp_const (-FunctionalInequalities.Probability.supportPoint μ)).add hμ)
  rw [hmap, covarianceBilin_map hμ' P v w, covarianceBilin_map_const_add,
    Submodule.adjoint_orthogonalProjectionOnto]
  rfl
