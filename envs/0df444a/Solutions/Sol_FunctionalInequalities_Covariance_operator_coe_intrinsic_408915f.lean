-- Prove2me | solution 1 for FunctionalInequalities.Covariance.operator_coe_intrinsic_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:50:07.581688+00:00
-- url     : https://prove2.me/submissions/9ac6ae5b-9a1c-446b-b2fb-42c5fb59dde6

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
import Theorems.Thm_FunctionalInequalities_Covariance_bilin_intrinsic_408915f

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
omit [BorelSpace E] in
/-- The barycenter of a probability law with finite second moment lies in its affine support. -/
theorem FunctionalInequalities.Probability.integral_id_mem_affineSupport (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) : (∫ x, x ∂(μ : Measure E)) ∈ affineSupport μ :=
  (affineSupport μ).convex.integral_mem (isClosed_affineSupport μ) (ae_mem_affineSupport μ)
    (hμ.integrable (by norm_num))
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
/-- The ambient covariance operator annihilates the orthogonal complement of the direction of the
affine support. -/
theorem FunctionalInequalities.Covariance.operator_apply_eq_zero_of_mem_orthogonal (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) {w : E} (hw : w ∈ (affineSupport μ).directionᗮ) :
    operator (μ : Measure E) w = 0 := by
  apply ext_inner_right ℝ
  intro y
  rw [operator_inner, inner_zero_left, covarianceBilin_apply hμ]
  have hm : (∫ x, id x ∂(μ : Measure E)) ∈ affineSupport μ := integral_id_mem_affineSupport μ hμ
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_mem_affineSupport μ] with z hz
  have hdir : z - ∫ x, id x ∂(μ : Measure E) ∈ (affineSupport μ).direction :=
    AffineSubspace.vsub_mem_direction hz hm
  show inner ℝ w (z - ∫ x, id x ∂(μ : Measure E)) * inner ℝ y (z - ∫ x, id x ∂(μ : Measure E)) = 0
  rw [Submodule.inner_left_of_mem_orthogonal hdir hw, zero_mul]
namespace FunctionalInequalities.Covariance
end FunctionalInequalities.Covariance
open FunctionalInequalities.Covariance in
/-- The ambient covariance operator restricts to the intrinsic covariance operator on the
direction space. -/
theorem solution (μ : ProbabilityMeasure E) (hμ : MemLp id 2 (μ : Measure E))
    (v : (FunctionalInequalities.Probability.affineSupport μ).direction) :
    FunctionalInequalities.Covariance.operator (μ : Measure E) v =
      (FunctionalInequalities.Covariance.operator (FunctionalInequalities.Probability.intrinsicMeasure μ : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) v : E) := by
  set P := (FunctionalInequalities.Probability.affineSupport μ).direction.orthogonalProjectionOnto
  set ν : Measure (FunctionalInequalities.Probability.affineSupport μ).direction := (FunctionalInequalities.Probability.intrinsicMeasure μ).toMeasure
  apply ext_inner_right ℝ
  intro y
  have hy : y = (P y : E) + (y - P y) := (add_sub_cancel _ _).symm
  have hperp : y - (P y : E) ∈ (FunctionalInequalities.Probability.affineSupport μ).directionᗮ := Submodule.sub_starProjection_mem_orthogonal y
  calc inner ℝ (FunctionalInequalities.Covariance.operator (μ : Measure E) v) y = covarianceBilin (μ : Measure E) v y :=
        FunctionalInequalities.Covariance.operator_inner _ _ _
    _ = covarianceBilin (μ : Measure E) v (P y) + covarianceBilin (μ : Measure E) v (y - P y) := by
        conv_lhs => rw [hy]
        rw [map_add]
    _ = covarianceBilin (μ : Measure E) v (P y) := by
        rw [covarianceBilin_comm (v : E) (y - P y), ← FunctionalInequalities.Covariance.operator_inner (μ : Measure E) (y - P y) v,
          FunctionalInequalities.Covariance.operator_apply_eq_zero_of_mem_orthogonal μ hμ hperp, inner_zero_left, add_zero]
    _ = covarianceBilin ν v (P y) := (FunctionalInequalities.Covariance.bilin_intrinsic_408915f μ hμ v (P y)).symm
    _ = inner ℝ (FunctionalInequalities.Covariance.operator ν v) (P y) := (FunctionalInequalities.Covariance.operator_inner _ _ _).symm
    _ = inner ℝ (FunctionalInequalities.Covariance.operator ν v : E) (P y : E) := rfl
    _ = inner ℝ (FunctionalInequalities.Covariance.operator ν v : E) y := by
        conv_rhs => rw [hy]
        rw [inner_add_right, Submodule.inner_right_of_mem_orthogonal (FunctionalInequalities.Covariance.operator ν v).property hperp,
          add_zero]
