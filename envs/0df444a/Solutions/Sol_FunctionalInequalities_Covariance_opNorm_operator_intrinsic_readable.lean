-- Prove2me | solution 1 for FunctionalInequalities.Covariance.opNorm_operator_intrinsic_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:43:20.063139+00:00
-- url     : https://prove2.me/submissions/8749f69b-5049-415a-aeea-acaec9ad512c

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic
import Theorems.Thm_FunctionalInequalities_Covariance_operator_coe_intrinsic_readable

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable [SecondCountableTopology E] [FiniteDimensional ℝ E]
section
omit [BorelSpace E] in
/-- The barycenter of a probability law with finite second moment lies in its affine support. -/
theorem FunctionalInequalities.Probability.integral_id_mem_affineSupport (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) : (∫ x, x ∂(μ : Measure E)) ∈ affineSupport μ :=
  (affineSupport μ).convex.integral_mem (isClosed_affineSupport μ) (ae_mem_affineSupport μ)
    (hμ.integrable (by norm_num))
end
open FunctionalInequalities.Probability
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
/-- Ambient and intrinsic covariance operators have the same operator norm. -/
theorem solution (μ : ProbabilityMeasure E) (hμ : MemLp id 2 (μ : Measure E)) :
    ‖FunctionalInequalities.Covariance.operator (FunctionalInequalities.Probability.intrinsicMeasure μ : Measure (FunctionalInequalities.Probability.affineSupport μ).direction)‖ =
      ‖FunctionalInequalities.Covariance.operator (μ : Measure E)‖ := by
  set P := (FunctionalInequalities.Probability.affineSupport μ).direction.orthogonalProjectionOnto
  set ν : Measure (FunctionalInequalities.Probability.affineSupport μ).direction := (FunctionalInequalities.Probability.intrinsicMeasure μ).toMeasure
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
    calc ‖FunctionalInequalities.Covariance.operator ν v‖ = ‖(FunctionalInequalities.Covariance.operator ν v : E)‖ := (Submodule.norm_coe _).symm
      _ = ‖FunctionalInequalities.Covariance.operator (μ : Measure E) v‖ := by rw [FunctionalInequalities.Covariance.operator_coe_intrinsic_readable μ hμ v]
      _ ≤ ‖FunctionalInequalities.Covariance.operator (μ : Measure E)‖ * ‖(v : E)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖FunctionalInequalities.Covariance.operator (μ : Measure E)‖ * ‖v‖ := by rw [Submodule.norm_coe]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y ↦ ?_
    have hy : y = (P y : E) + (y - P y) := (add_sub_cancel _ _).symm
    have hperp : y - (P y : E) ∈ (FunctionalInequalities.Probability.affineSupport μ).directionᗮ := Submodule.sub_starProjection_mem_orthogonal y
    have h0 : FunctionalInequalities.Covariance.operator (μ : Measure E) (y - P y) = 0 :=
      FunctionalInequalities.Covariance.operator_apply_eq_zero_of_mem_orthogonal μ hμ hperp
    calc ‖FunctionalInequalities.Covariance.operator (μ : Measure E) y‖
        = ‖FunctionalInequalities.Covariance.operator (μ : Measure E) (P y) + FunctionalInequalities.Covariance.operator (μ : Measure E) (y - P y)‖ := by
          conv_lhs => rw [hy]
          rw [map_add]
      _ = ‖(FunctionalInequalities.Covariance.operator ν (P y) : E)‖ := by rw [h0, add_zero, FunctionalInequalities.Covariance.operator_coe_intrinsic_readable μ hμ]
      _ = ‖FunctionalInequalities.Covariance.operator ν (P y)‖ := Submodule.norm_coe _
      _ ≤ ‖FunctionalInequalities.Covariance.operator ν‖ * ‖P y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖FunctionalInequalities.Covariance.operator ν‖ * ‖y‖ :=
          mul_le_mul_of_nonneg_left ((FunctionalInequalities.Probability.affineSupport μ).direction.norm_orthogonalProjectionOnto_apply_le y) (norm_nonneg _)
