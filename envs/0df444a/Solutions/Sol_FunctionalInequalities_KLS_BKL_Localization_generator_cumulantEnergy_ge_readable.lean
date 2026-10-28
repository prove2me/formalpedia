-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.generator_cumulantEnergy_ge_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:25.54608+00:00
-- url     : https://prove2.me/submissions/b5a724fd-e40d-4a10-87ea-2cab1fecf1e0

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Positive
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Positivity
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_IsotropicSupport
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_VectorGenerator
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Generator
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_contDiffAt_energyForm_readable
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_deriv_deriv_energyForm_line_readable
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_drift_expression_ge_readable
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_fderiv_fderiv_apply_eq_deriv_deriv_line_readable
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_hasDerivAt_energyForm_line_readable
import Theorems.Thm_FunctionalInequalities_Analysis_inner_self_pos_of_isPositive_of_isUnit_readable
import Theorems.Thm_FunctionalInequalities_Covariance_inner_operator_self_pos_of_affineSupport_eq_top_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_cumulantEnergy_eq_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_stdMatrix_conjugatedNoiseOperator_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_sum_sq_conjugatedNoiseMatrix_mulVec_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_cumulantEnergy_succ_eq_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_posteriorCovariance_joint_readable

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]
/-- A measurable statistic bounded on the support is in `L²` of the tilt. -/
theorem FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact (μ : ProbabilityMeasure Ω) (hc : IsCompact (μ : Measure Ω).support)
    {φ f : Ω → ℝ} (hφ : Continuous φ) (hf : Measurable f) {C : ℝ}
    (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    MemLp f 2 ((μ : Measure Ω).tilted φ) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  apply (integrable_tilted_iff (integrable_exp_of_compact μ hc hφ) (fun x => f x ^ 2)).mpr
  have hd : Integrable (fun x => Real.exp (φ x) * f x ^ 2) (μ : Measure Ω) := by
    apply integrable_exp_mul_of_compact μ hc hφ (hf.pow_const 2) (C := C ^ 2) (sq_nonneg C)
    intro x hx
    rw [norm_pow]
    have hB : 0 ≤ C := (norm_nonneg (f x)).trans (hb x hx)
    exact (sq_le_sq₀ (norm_nonneg _) hB).mpr (hb x hx)
  simpa only [smul_eq_mul] using hd
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
/-- Continuous statistics are in `L²` of every posterior of a compactly supported prior. -/
theorem FunctionalInequalities.Probability.Posterior.memLp_two_tilted_quadraticExponent_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E)
    {f : E → ℝ} (hf : Continuous f) :
    MemLp f 2 ((μ : Measure E).tilted (quadraticExponent c Q)) := by
  obtain ⟨C, _hC, hb⟩ := exists_bound_on_support_of_compact μ hc hf
  have hφ : Continuous (quadraticExponent c Q) := by unfold quadraticExponent; fun_prop
  exact memLp_two_tilted_of_compact μ hc hφ hf.measurable hb
end
end
end

section
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
section
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
end
end
end

section
open scoped RealInnerProductSpace
section FiniteDimensional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- A strictly positive operator (`⟪T v, v⟫ > 0` for `v ≠ 0`) on a finite-dimensional space is a unit. -/
theorem FunctionalInequalities.Analysis.isUnit_of_inner_self_pos (T : E →L[ℝ] E)
    (hpos : ∀ v : E, v ≠ 0 → 0 < ⟪T v, v⟫) : IsUnit T := by
  apply ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr
  apply (LinearMap.isUnit_iff_ker_eq_bot T.toLinearMap).mpr
  apply bot_unique
  intro v hv
  have hv' : T v = 0 := hv
  change v = 0
  by_contra hne
  have hp := hpos v hne
  rw [hv', inner_zero_left] at hp
  exact (lt_irrefl 0) hp
end FiniteDimensional
end

section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- An injective covariance operator forces full affine support. -/
theorem FunctionalInequalities.Probability.affineSupport_eq_top_of_covariance_injective (μ : ProbabilityMeasure E)
    (h2 : MemLp id 2 (μ : Measure E)) (hinj : Function.Injective (Covariance.operator (μ : Measure E))) :
    Probability.affineSupport μ = ⊤ := by
  have hperp : (Probability.affineSupport μ).directionᗮ = ⊥ := by
    apply bot_unique
    intro w hw
    have h := Covariance.operator_apply_eq_zero_of_mem_orthogonal μ h2 hw
    have hz : w = 0 := hinj (h.trans (map_zero _).symm)
    simpa only [Submodule.mem_bot] using hz
  have hdir : (Probability.affineSupport μ).direction = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hperp
  have hne : (Probability.affineSupport μ : Set E).Nonempty :=
    ⟨Probability.origin μ, (Probability.origin μ).property⟩
  exact (AffineSubspace.direction_eq_top_iff_of_nonempty hne).mp hdir
/-- The covariance operator is self-adjoint. -/
theorem FunctionalInequalities.Covariance.operator_isSelfAdjoint (μ : Measure E) : IsSelfAdjoint (Covariance.operator μ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪Covariance.operator μ x, y⟫ = ⟪x, Covariance.operator μ y⟫
  calc
    ⟪Covariance.operator μ x, y⟫ = covarianceBilin μ x y := Covariance.operator_inner μ x y
    _ = covarianceBilin μ y x := covarianceBilin_comm x y
    _ = ⟪Covariance.operator μ y, x⟫ := (Covariance.operator_inner μ y x).symm
    _ = ⟪x, Covariance.operator μ y⟫ := real_inner_comm _ _
end
end

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
universe u v
section TiltAbsoluteContinuity
variable {Ω : Type*} [MeasurableSpace Ω]
/-- A normalized tilt has the same topological support as the base law. -/
theorem FunctionalInequalities.Probability.support_tilted_eq [TopologicalSpace Ω] (μ : Measure Ω) {φ : Ω → ℝ}
    (hi : Integrable (fun x => Real.exp (φ x)) μ) : (μ.tilted φ).support = μ.support :=
  Set.Subset.antisymm (tilted_absolutelyContinuous μ φ).support_mono
    (absolutelyContinuous_tilted hi).support_mono
end TiltAbsoluteContinuity
end
end
end

section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The posterior has the same support as the prior. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_support (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    (compactPosterior μ hc c Q : Measure E).support = (μ : Measure E).support := by
  exact Probability.support_tilted_eq _ (integrable_exp_of_compact μ hc (by unfold quadraticExponent; fun_prop))
/-- The posterior has the same affine support as the prior. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_affineSupport (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    Probability.affineSupport (compactPosterior μ hc c Q) = Probability.affineSupport μ := by
  unfold Probability.affineSupport
  rw [compactPosterior_support]
/-- The posterior has finite second moment. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_memLp_id_two (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    MemLp id 2 (compactPosterior μ hc c Q : Measure E) := by
  change MemLp id 2 ((μ : Measure E).tilted (quadraticExponent c Q))
  have hn : MemLp (fun x : E => ‖x‖) 2 ((μ : Measure E).tilted (quadraticExponent c Q)) :=
    memLp_two_tilted_quadraticExponent_of_compact μ hc c Q continuous_norm
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
  exact (memLp_two_iff_integrable_sq hn.aestronglyMeasurable).1 hn
/-- For a prior with full affine support every posterior has strictly positive covariance. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_covariance_pos_of_affineSupport_eq_top (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hfull : Probability.affineSupport μ = ⊤)
    (c : E) (Q : E →L[ℝ] E) {v : E} (hv : v ≠ 0) :
    0 < ⟪Covariance.operator (compactPosterior μ hc c Q : Measure E) v, v⟫ := by
  apply Covariance.inner_operator_self_pos_of_affineSupport_eq_top_readable (compactPosterior μ hc c Q)
    (compactPosterior_memLp_id_two μ hc c Q) ?_ hv
  rw [compactPosterior_affineSupport, hfull]
end
end
end

section
open MeasureTheory
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- An isotropic law has full affine support. -/
theorem FunctionalInequalities.KLS.Isotropic.affineSupport_eq_top {μ : ProbabilityMeasure E} (hiso : KLS.Isotropic μ) :
    Probability.affineSupport μ = ⊤ := by
  apply Probability.affineSupport_eq_top_of_covariance_injective μ hiso.memLp_two
  rw [hiso.covariance_identity]
  exact fun _ _ h => h
end
end

section
noncomputable section
open scoped RealInnerProductSpace MatrixOrder
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section OperatorMatrix
open Matrix
variable [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_operatorOfMatrix (b : OrthonormalBasis ι ℝ E) (M : Matrix ι ι ℝ) :
    operatorMatrix b (operatorOfMatrix b M) = M := by
  exact (LinearMap.toMatrixOrthonormal b).apply_symm_apply M
@[simp] theorem FunctionalInequalities.Analysis.operatorOfMatrix_operatorMatrix (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    operatorOfMatrix b (operatorMatrix b T) = T := by
  exact congrArg (fun f : E →ₗ[ℝ] E => f.toContinuousLinearMap)
    ((LinearMap.toMatrixOrthonormal b).symm_apply_apply T.toLinearMap)
theorem FunctionalInequalities.Analysis.operatorMatrix_injective (b : OrthonormalBasis ι ℝ E) : Function.Injective (operatorMatrix b) := by
  intro S T h
  have := congrArg (operatorOfMatrix b) h
  simpa only [operatorOfMatrix_operatorMatrix] using this
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_mul (b : OrthonormalBasis ι ℝ E) (S T : E →L[ℝ] E) :
    operatorMatrix b (S * T) = operatorMatrix b S * operatorMatrix b T := by
  exact map_mul (LinearMap.toMatrixOrthonormal b) S.toLinearMap T.toLinearMap
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_one (b : OrthonormalBasis ι ℝ E) :
    operatorMatrix b (1 : E →L[ℝ] E) = 1 := by
  exact map_one (LinearMap.toMatrixOrthonormal b)
/-- The matrix is positive semidefinite iff the operator is positive (Mathlib `posSemidef_toMatrix_iff`). -/
theorem FunctionalInequalities.Analysis.operatorMatrix_posSemidef_iff (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    (operatorMatrix b T).PosSemidef ↔ T.IsPositive :=
  LinearMap.posSemidef_toMatrix_iff b
theorem FunctionalInequalities.Analysis.operatorOfMatrix_isPositive (b : OrthonormalBasis ι ℝ E) (M : Matrix ι ι ℝ)
    (hM : M.PosSemidef) : (operatorOfMatrix b M).IsPositive := by
  apply (operatorMatrix_posSemidef_iff b _).mp
  simpa only [operatorMatrix_operatorOfMatrix] using hM
/-- The matrix inverse of a unit's matrix is the matrix of `Ring.inverse`. -/
theorem FunctionalInequalities.Analysis.operatorMatrix_ringInverse (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) (hA : IsUnit A) :
    (operatorMatrix b A)⁻¹ = operatorMatrix b (Ring.inverse A) := by
  apply Matrix.inv_eq_right_inv
  rw [← operatorMatrix_mul, Ring.mul_inverse_cancel A hA, operatorMatrix_one]
theorem FunctionalInequalities.Analysis.operatorMatrix_isUnit_iff (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    IsUnit (operatorMatrix b A) ↔ IsUnit A := by
  exact (LinearMap.isUnit_toMatrix_iff b.toBasis).trans
    ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.symm
end OperatorMatrix
end
end
end

section
noncomputable section
open scoped MatrixOrder RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_inverseSqrtIn (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    operatorMatrix b (inverseSqrtIn b A) = CFC.sqrt ((operatorMatrix b A)⁻¹) :=
  operatorMatrix_operatorOfMatrix b _
theorem FunctionalInequalities.Analysis.inverseSqrtIn_isPositive (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    (inverseSqrtIn b A).IsPositive :=
  operatorOfMatrix_isPositive b _ (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _))
theorem FunctionalInequalities.Analysis.inverseSqrtIn_isSelfAdjoint (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    IsSelfAdjoint (inverseSqrtIn b A) := (inverseSqrtIn_isPositive b A).isSelfAdjoint
/-- `σ² = Ring.inverse A` for a positive unit `A`. -/
theorem FunctionalInequalities.Analysis.inverseSqrtIn_mul_self (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) :
    inverseSqrtIn b A * inverseSqrtIn b A = Ring.inverse A := by
  apply operatorMatrix_injective b
  rw [operatorMatrix_mul]
  rw [operatorMatrix_inverseSqrtIn]
  rw [CFC.sqrt_mul_sqrt_self _ ((operatorMatrix_posSemidef_iff b A).mpr hpos).inv.nonneg,
    operatorMatrix_ringInverse b A hunit]
/-- `σ σ* = Ring.inverse A`. -/
theorem FunctionalInequalities.Analysis.inverseSqrtIn_mul_adjoint (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) :
    inverseSqrtIn b A * (inverseSqrtIn b A).adjoint = Ring.inverse A := by
  have hsa : (inverseSqrtIn b A).adjoint = inverseSqrtIn b A :=
    inverseSqrtIn_isSelfAdjoint b A
  rw [hsa]
  exact inverseSqrtIn_mul_self b A hpos hunit
/-- `A σσ* = 1 = σσ* A`. -/
theorem FunctionalInequalities.Analysis.inverseSqrtIn_mul_adjoint_cancel (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) :
    A * (inverseSqrtIn b A * (inverseSqrtIn b A).adjoint) = 1 ∧
      (inverseSqrtIn b A * (inverseSqrtIn b A).adjoint) * A = 1 := by
  rw [inverseSqrtIn_mul_adjoint b A hpos hunit]
  exact ⟨Ring.mul_inverse_cancel A hunit, Ring.inverse_mul_cancel A hunit⟩
theorem FunctionalInequalities.Analysis.inverseSqrtIn_isUnit (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) : IsUnit (inverseSqrtIn b A) := by
  have hp : (operatorMatrix b A).PosDef :=
    ((operatorMatrix_posSemidef_iff b A).mpr hpos).posDef_iff_isUnit.mpr
      ((operatorMatrix_isUnit_iff b A).mpr hunit)
  apply (operatorMatrix_isUnit_iff b _).mp
  rw [operatorMatrix_inverseSqrtIn]
  exact (IsStrictlyPositive.sqrt _ hp.inv.isStrictlyPositive).isUnit
theorem FunctionalInequalities.Analysis.inverseSqrtIn_inner_self_pos (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) {v : E} (hv : v ≠ 0) :
    0 < ⟪inverseSqrtIn b A v, v⟫ :=
  inner_self_pos_of_isPositive_of_isUnit_readable b _ (inverseSqrtIn_isPositive b A)
    (inverseSqrtIn_isUnit b A hpos hunit) hv
/-- **Specification of `A^{-1/2}`** for a positive unit `A`: positive, self-adjoint, `σ² = σσ* = Ring.inverse A`,
`A σσ* = σσ* A = 1`. -/
theorem FunctionalInequalities.Analysis.inverseSqrt_spec (A : E →L[ℝ] E) (hpos : A.IsPositive) (hunit : IsUnit A) :
    (inverseSqrt A).IsPositive ∧ IsSelfAdjoint (inverseSqrt A) ∧
      inverseSqrt A * inverseSqrt A = Ring.inverse A ∧
      inverseSqrt A * (inverseSqrt A).adjoint = Ring.inverse A ∧
      A * (inverseSqrt A * (inverseSqrt A).adjoint) = 1 ∧
      (inverseSqrt A * (inverseSqrt A).adjoint) * A = 1 := by
  exact ⟨inverseSqrtIn_isPositive _ A, inverseSqrtIn_isSelfAdjoint _ A,
    inverseSqrtIn_mul_self _ A hpos hunit, inverseSqrtIn_mul_adjoint _ A hpos hunit,
    inverseSqrtIn_mul_adjoint_cancel _ A hpos hunit⟩
end
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
open Set
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- For a compactly supported isotropic prior every posterior has strictly positive covariance. -/
theorem FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_pos (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ)
    (c : E) (Q : E →L[ℝ] E) {v : E} (hv : v ≠ 0) :
    0 < ⟪Covariance.operator (compactPosterior μ hc c Q : Measure E) v, v⟫ :=
  compactPosterior_covariance_pos_of_affineSupport_eq_top μ hc (hiso.affineSupport_eq_top) c Q hv
/-- The posterior covariance is a unit. -/
theorem FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_isUnit (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    IsUnit (Covariance.operator (compactPosterior μ hc c Q : Measure E)) :=
  Analysis.isUnit_of_inner_self_pos _ (fun _ hv => Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hv)
/-- The posterior covariance is a positive operator. -/
theorem FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_isPositive (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    (Covariance.operator (compactPosterior μ hc c Q : Measure E)).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff' _).mpr
  refine ⟨Covariance.operator_isSelfAdjoint _, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · exact (Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hv).le
/-- **The diffusion coefficient `A^{-1/2}` of (67)**: for a compactly supported isotropic prior and every finite
`(c, Q)` (including `0`, negative `Q`, rank zero), `σ = inverseSqrt (Cov μ_{c,Q})` is self-adjoint, positive,
strictly positive, `σ² = σσ* = Cov⁻¹` and `Cov σσ* = σσ* Cov = 1`. Coefficient algebra only; no regularity,
SDE, Itô or martingale statement. -/
theorem FunctionalInequalities.KLS.Isotropic.compactPosterior_inverseSqrt_spec (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    let A := Covariance.operator (compactPosterior μ hc c Q : Measure E)
    let σ := inverseSqrt A
    IsSelfAdjoint σ ∧ σ.IsPositive ∧ (∀ v : E, v ≠ 0 → 0 < ⟪σ v, v⟫) ∧
      σ * σ = Ring.inverse A ∧ σ * σ.adjoint = Ring.inverse A ∧
      A * (σ * σ.adjoint) = 1 ∧ (σ * σ.adjoint) * A = 1 := by
  dsimp only
  let A := Covariance.operator (compactPosterior μ hc c Q : Measure E)
  have hp := Isotropic.compactPosterior_covariance_isPositive μ hc hiso c Q
  have hu := Isotropic.compactPosterior_covariance_isUnit μ hc hiso c Q
  obtain ⟨hpos, hsa, hsquare, hgram, hl, hr⟩ := inverseSqrt_spec A hp hu
  exact ⟨hsa, hpos, fun _ hv => inverseSqrtIn_inner_self_pos _ A hp hu hv,
    hsquare, hgram, hl, hr⟩
variable {ι : Type*} [Fintype ι]
end
end
end

section
noncomputable section
open Matrix
open scoped RealInnerProductSpace
section S3Bf2EnergyFormFirstOrder
section
variable {n r : ℕ}
/-- The directional derivative is the derivative along the line. -/
theorem FunctionalInequalities.Analysis.CoordinateTensor.fderiv_apply_eq_deriv_line {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : W → ℝ} {y : W}
    (hΦ : DifferentiableAt ℝ Φ y) (v : W) :
    fderiv ℝ Φ y v = deriv (fun ε : ℝ => Φ (y + ε • v)) 0 := by
  let line : ℝ → W := fun ε => y + ε • v
  have hl : HasDerivAt line v 0 := by
    simpa only [line, id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y)
  have hp : HasFDerivAt Φ (fderiv ℝ Φ y) (line 0) := by
    simpa [line] using hΦ.hasFDerivAt
  have hd := (hp.comp_hasDerivAt 0 hl).deriv.symm
  change fderiv ℝ Φ y v = deriv (fun ε : ℝ => Φ (y + ε • v)) 0 at hd
  exact hd
set_option maxHeartbeats 800000 in
/-- **BKL (88), first order**: `DF(Id, T)[(H, X)] = 2⟨T, X⟩ − ⟨T, Σ_H T⟩`. -/
theorem FunctionalInequalities.Analysis.CoordinateTensor.fderiv_energyForm_one (T : (Fin r → Fin n) → ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (X : (Fin r → Fin n) → ℝ) :
    fderiv ℝ (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
        energyForm q.1 q.2) (1, T) (H, X) =
      2 * inner T X - inner T (actSum (stdMatrix H) T) := by
  have hdiff :=
    (contDiffAt_energyForm_readable
      (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      isUnit_one T).differentiableAt (by norm_num)
  rw [fderiv_apply_eq_deriv_line hdiff (H, X)]
  change deriv (fun t : ℝ => energyForm (1 + t • H) (T + t • X)) 0 =
    2 * inner T X - inner T (actSum (stdMatrix H) T)
  exact (hasDerivAt_energyForm_line_readable T H X).deriv
end
end S3Bf2EnergyFormFirstOrder
section S3Bf3B2SecondOrderCore
section
variable {n r : ℕ}
/-- **BKL (88), second order**: for symmetric `H`,
`D²F(Id, T)[(H, X), (H, X)] = 2 (|X|² − 2⟨X, Σ_H T⟩ + ½|Σ_H T|² + ½ Σ_s |H^{(s)} T|²)`. -/
theorem FunctionalInequalities.Analysis.CoordinateTensor.fderiv_fderiv_energyForm_one (T : (Fin r → Fin n) → ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : IsSelfAdjoint H)
    (X : (Fin r → Fin n) → ℝ) :
    fderiv ℝ (fderiv ℝ (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
        energyForm q.1 q.2)) (1, T) (H, X) (H, X) =
      2 * (inner X X - 2 * inner X (actSum (stdMatrix H) T)
        + (1 / 2 : ℝ) * inner (actSum (stdMatrix H) T) (actSum (stdMatrix H) T)
        + (1 / 2 : ℝ) * ∑ s, inner (actOn (stdMatrix H) s T) (actOn (stdMatrix H) s T)) := by
  have hdiff :=
    contDiffAt_energyForm_readable
      (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) isUnit_one T
  rw [fderiv_fderiv_apply_eq_deriv_deriv_line_readable hdiff (H, X)]
  change deriv (deriv fun ε : ℝ => energyForm (1 + ε • H) (T + ε • X)) 0 = _
  exact deriv_deriv_energyForm_line_readable T H hH X
end
end S3Bf3B2SecondOrderCore
end
end

section
noncomputable section
open scoped Topology
section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
section NormedSpace
variable {W W' : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W'] [NormedSpace ℝ W']
/-- The derivative of a continuous linear map applied to a differentiable function. -/
theorem FunctionalInequalities.Probability.Diffusion.fderiv_clm_comp_apply_vec (ℓ : W →L[ℝ] W') {G : V → W} {x : V}
    (hG : DifferentiableAt ℝ G x) (v : V) :
    fderiv ℝ (fun y => ℓ (G y)) x v = ℓ (fderiv ℝ G x v) := by
  exact congrArg (fun q : V →L[ℝ] W' => q v)
    (ℓ.hasFDerivAt.comp x hG.hasFDerivAt).fderiv
end NormedSpace
end
end
end

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
  FunctionalInequalities.Analysis.CoordinateTensor
section
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
private theorem FunctionalInequalities.KLS.BKL.Localization.covariance_contDiff_two :
    ContDiff ℝ 2 (cov μ hc) :=
  (contDiff_posteriorCovariance_joint_readable μ hc).of_le
    (WithTop.coe_le_coe.mpr le_top)
private theorem FunctionalInequalities.KLS.BKL.Localization.derivative_cov_inner (p v : Param n)
    (x y : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun q => ⟪cov μ hc q x, y⟫) p v =
      ⟪fderiv ℝ (cov μ hc) p v x, y⟫ := by
  have hd : DifferentiableAt ℝ (cov μ hc) p :=
    (covariance_contDiff_two μ hc).contDiffAt.differentiableAt (by norm_num)
  have h := fderiv_clm_comp_apply_vec
    ((innerSL ℝ y).comp (ContinuousLinearMap.apply ℝ _ x)) hd v
  change
    fderiv ℝ (fun q => ⟪y, cov μ hc q x⟫) p v =
      ⟪y, fderiv ℝ (cov μ hc) p v x⟫ at h
  simpa only [real_inner_comm] using h
private theorem FunctionalInequalities.KLS.BKL.Localization.derivative_cov_symmetric (p v : Param n) :
    IsSelfAdjoint (fderiv ℝ (cov μ hc) p v) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have hf :
      (fun q => ⟪cov μ hc q x, y⟫) =
        (fun q => ⟪cov μ hc q y, x⟫) := by
    funext q
    have hs : IsSelfAdjoint (cov μ hc q) :=
      Covariance.operator_isSelfAdjoint _
    calc
      ⟪cov μ hc q x, y⟫ = ⟪x, cov μ hc q y⟫ :=
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hs) x y
      _ = ⟪cov μ hc q y, x⟫ := real_inner_comm _ _
  change
    ⟪fderiv ℝ (cov μ hc) p v x, y⟫ =
      ⟪x, fderiv ℝ (cov μ hc) p v y⟫
  calc
    ⟪fderiv ℝ (cov μ hc) p v x, y⟫ =
        fderiv ℝ (fun q => ⟪cov μ hc q x, y⟫) p v :=
      (derivative_cov_inner μ hc p v x y).symm
    _ = fderiv ℝ (fun q => ⟪cov μ hc q y, x⟫) p v := by rw [hf]
    _ = ⟪fderiv ℝ (cov μ hc) p v y, x⟫ :=
      derivative_cov_inner μ hc p v y x
    _ = ⟪x, fderiv ℝ (cov μ hc) p v y⟫ := real_inner_comm _ _
theorem FunctionalInequalities.KLS.BKL.Localization.inner_energyTensor_self (p : Param n) (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    inner (energyTensor μ hc p r u) (energyTensor μ hc p r u) =
      cumulantEnergy
        (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) r u := by
  classical
  simp only [CoordinateTensor.inner, energyTensor, cumulantEnergy, pow_two, cov]
theorem FunctionalInequalities.KLS.BKL.Localization.sum_inner_noiseTensor_self (p : Param n) (r : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    ∑ k, inner (noiseTensor μ hc p r u k) (noiseTensor μ hc p r u k) =
      cumulantEnergy
        (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
        (r + 1) u := by
  classical
  rw [cumulantEnergy_succ_eq_readable]
  simp only [CoordinateTensor.inner, noiseTensor, pow_two]
  rw [Finset.sum_comm]
  rfl
theorem FunctionalInequalities.KLS.BKL.Localization.isSelfAdjoint_conjugatedNoiseOperator (hiso : KLS.Isotropic μ)
    (p : Param n) (k : Fin n) :
    IsSelfAdjoint (conjugatedNoiseOperator μ hc p k) := by
  let P := inverseSqrt (cov μ hc p)
  let D := fderiv ℝ (cov μ hc) p (noise μ hc p k)
  have hP : IsSelfAdjoint P :=
    (Isotropic.compactPosterior_inverseSqrt_spec μ hc hiso p.1 p.2).1
  have hD : IsSelfAdjoint D :=
    derivative_cov_symmetric μ hc p (noise μ hc p k)
  have hsP := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP
  have hsD := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hD
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪P (D (P x)), y⟫ = ⟪x, P (D (P y))⟫
  calc
    ⟪P (D (P x)), y⟫ = ⟪D (P x), P y⟫ := hsP _ _
    _ = ⟪P x, D (P y)⟫ := hsD _ _
    _ = ⟪x, P (D (P y))⟫ := hsP _ _
end
section S3BLemma51Assembly
open scoped RealInnerProductSpace
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
private lemma FunctionalInequalities.KLS.BKL.Localization.stdMatrix_neg_one :
    stdMatrix (-1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      (-1 : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  ext i k
  change
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
      -(EuclideanSpace.basisFun (Fin n) ℝ k)⟫ =
        -((1 : Matrix (Fin n) (Fin n) ℝ) i k)
  rw [_root_.inner_neg_right, OrthonormalBasis.inner_eq_ite, Matrix.one_apply]
private lemma FunctionalInequalities.KLS.BKL.Localization.actOn_neg_one {r : ℕ} (s : Fin r) (T : (Fin r → Fin n) → ℝ) :
    actOn (-1 : Matrix (Fin n) (Fin n) ℝ) s T = -T := by
  classical
  ext J
  simp [actOn, Matrix.one_apply, ite_mul]
private lemma FunctionalInequalities.KLS.BKL.Localization.actSum_neg_one {r : ℕ} (T : (Fin r → Fin n) → ℝ) :
    actSum (-1 : Matrix (Fin n) (Fin n) ℝ) T = -(r : ℝ) • T := by
  classical
  ext J
  simp [actSum, actOn_neg_one, Finset.sum_const]
private lemma FunctionalInequalities.KLS.BKL.Localization.tensor_inner_smul_right {r : ℕ}
    (A B : (Fin r → Fin n) → ℝ) (c : ℝ) :
    inner A (c • B) = c * inner A B := by
  classical
  simp only [CoordinateTensor.inner, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ J, A J * (c * B J)) = ∑ J, c * (A J * B J) := by
      apply Finset.sum_congr rfl
      intro J _
      ring
    _ = c * ∑ J, A J * B J := (Finset.mul_sum _ _ _).symm
private lemma FunctionalInequalities.KLS.BKL.Localization.tensor_inner_neg_right {r : ℕ}
    (A B : (Fin r → Fin n) → ℝ) :
    inner A (-B) = -inner A B := by
  simp [CoordinateTensor.inner]
private lemma FunctionalInequalities.KLS.BKL.Localization.tensor_inner_add_right {r : ℕ}
    (A B C : (Fin r → Fin n) → ℝ) :
    inner A (B + C) = inner A B + inner A C := by
  simp [CoordinateTensor.inner, mul_add, Finset.sum_add_distrib]
private lemma FunctionalInequalities.KLS.BKL.Localization.stdMatrix_entry_symmetry
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : IsSelfAdjoint A) :
    ∀ a b, stdMatrix A a b = stdMatrix A b a := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  intro a b
  change
    ⟪EuclideanSpace.basisFun (Fin n) ℝ a,
        A (EuclideanSpace.basisFun (Fin n) ℝ b)⟫ =
      ⟪EuclideanSpace.basisFun (Fin n) ℝ b,
        A (EuclideanSpace.basisFun (Fin n) ℝ a)⟫
  calc
    ⟪EuclideanSpace.basisFun (Fin n) ℝ a,
        A (EuclideanSpace.basisFun (Fin n) ℝ b)⟫ =
        ⟪A (EuclideanSpace.basisFun (Fin n) ℝ a),
          EuclideanSpace.basisFun (Fin n) ℝ b⟫ := (hs _ _).symm
    _ = ⟪EuclideanSpace.basisFun (Fin n) ℝ b,
          A (EuclideanSpace.basisFun (Fin n) ℝ a)⟫ := real_inner_comm _ _
/-- **BKL Lemma 5.1, (80), in generator form** with the explicit constant `C = 17`: for a compactly supported isotropic
log-concave prior, the third-order bound `CumulantBoundCompact 2 8` (BKL (79) via Lemma 4.2), `m = r + 1 ≥ 3`, a direction
`u` and a parameter `p` with symmetric positive semidefinite `Q`, the generator of (67) applied to the cumulant energy
`E_m(q) = |κ_m(μ_q)(u)|²_q` satisfies
`𝓛E_m(p) ≥ ½ E_{m+1}(p) − 17 m² E_m(p) − 2 ⟨κ_m(p)(u), L_m(p)(u)⟩_p`,
where `⟨κ_m(u), L_m(u)⟩_p = Σ_K κ_m(u, σ e_K) · L_m(u, σ e_K)` with `σ = A(p)^{-1/2}` and `L_m` the middle term (72)
(`lowerDrift`, slot `0`). -/
theorem solution (hiso : FunctionalInequalities.KLS.Isotropic μ) (hLC : FunctionalInequalities.KLS.LogConcave μ)
    (h8 : FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBoundCompact 2 8) {r : ℕ} (hr : 2 ≤ r)
    (u : EuclideanSpace ℝ (Fin n)) (p : FunctionalInequalities.KLS.BKL.Localization.Param n) (hSym : IsSelfAdjoint p.2) (hQ : ∀ x, 0 ≤ ⟪p.2 x, x⟫) :
    (1 / 2 : ℝ) * FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (r + 1) u
        - 17 * ((r : ℝ) + 1) ^ 2 *
          FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) r u
        - 2 * ∑ K : Fin r → Fin n,
            FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (r + 1)
                (Fin.cons u fun s => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ (K s))) *
              FunctionalInequalities.KLS.BKL.lowerDrift (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
                (Fin.cons u fun s => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ (K s))) 0 ≤
      FunctionalInequalities.KLS.BKL.Localization.generator μ hc
        (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) r u) p := by
  classical
  let T : (Fin r → Fin n) → ℝ := FunctionalInequalities.KLS.BKL.Localization.energyTensor μ hc p r u
  let L : (Fin r → Fin n) → ℝ := FunctionalInequalities.KLS.BKL.Localization.lowerTensor μ hc p r u
  let W : Fin n → (Fin r → Fin n) → ℝ := FunctionalInequalities.KLS.BKL.Localization.noiseTensor μ hc p r u
  let H : Fin n → Matrix (Fin n) (Fin n) ℝ :=
    fun i => FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseMatrix μ hc p i

  have hfirst :
      fderiv ℝ
          (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ×
            ((Fin r → Fin n) → ℝ) => FunctionalInequalities.Analysis.CoordinateTensor.energyForm q.1 q.2)
          (1, T) (-1, -(((r : ℝ) + 1) • T + L)) =
        -(((r : ℝ) + 1) + 1) * FunctionalInequalities.Analysis.CoordinateTensor.inner T T - 2 * FunctionalInequalities.Analysis.CoordinateTensor.inner T L := by
    rw [FunctionalInequalities.Analysis.CoordinateTensor.fderiv_energyForm_one, FunctionalInequalities.KLS.BKL.Localization.stdMatrix_neg_one, FunctionalInequalities.KLS.BKL.Localization.actSum_neg_one]
    simp only [FunctionalInequalities.KLS.BKL.Localization.tensor_inner_neg_right, FunctionalInequalities.KLS.BKL.Localization.tensor_inner_add_right, FunctionalInequalities.KLS.BKL.Localization.tensor_inner_smul_right]
    ring

  have hsecond (i : Fin n) :
      fderiv ℝ
          (fderiv ℝ
            (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ×
              ((Fin r → Fin n) → ℝ) => FunctionalInequalities.Analysis.CoordinateTensor.energyForm q.1 q.2))
          (1, T)
          (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseOperator μ hc p i, W i)
          (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseOperator μ hc p i, W i) =
        2 * (FunctionalInequalities.Analysis.CoordinateTensor.inner (W i) (W i)
          - 2 * FunctionalInequalities.Analysis.CoordinateTensor.inner (W i) (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T)
          + (1 / 2 : ℝ) * FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T) (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T)
          + (1 / 2 : ℝ) * ∑ s,
              FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn (H i) s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn (H i) s T)) := by
    rw [FunctionalInequalities.Analysis.CoordinateTensor.fderiv_fderiv_energyForm_one T
      (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseOperator μ hc p i)
      (FunctionalInequalities.KLS.BKL.Localization.isSelfAdjoint_conjugatedNoiseOperator μ hc hiso p i) (W i)]
    rw [FunctionalInequalities.KLS.BKL.Localization.stdMatrix_conjugatedNoiseOperator_readable μ hc hiso p i]

  have hHerm : ∀ i, (H i).IsHermitian := by
    intro i
    change (H i).conjTranspose = H i
    ext a b
    change FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseMatrix μ hc p i b a =
      FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseMatrix μ hc p i a b
    rw [← FunctionalInequalities.KLS.BKL.Localization.stdMatrix_conjugatedNoiseOperator_readable μ hc hiso p i]
    exact FunctionalInequalities.KLS.BKL.Localization.stdMatrix_entry_symmetry
      (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseOperator μ hc p i)
      (FunctionalInequalities.KLS.BKL.Localization.isSelfAdjoint_conjugatedNoiseOperator μ hc hiso p i) b a

  have h8' :
      ∀ v : Fin n → ℝ,
        ∑ i, ∑ a, (∑ b, H i a b * v b) ^ 2 ≤ 8 * ∑ a, v a ^ 2 := by
    intro v
    exact FunctionalInequalities.KLS.BKL.Localization.sum_sq_conjugatedNoiseMatrix_mulVec_le_readable μ hc hiso hLC h8 p hSym hQ v

  have hT :
      FunctionalInequalities.Analysis.CoordinateTensor.inner T T =
        FunctionalInequalities.KLS.BKL.cumulantEnergy
          (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) r u :=
    FunctionalInequalities.KLS.BKL.Localization.inner_energyTensor_self μ hc p r u

  have hW :
      ∑ i, FunctionalInequalities.Analysis.CoordinateTensor.inner (W i) (W i) =
        FunctionalInequalities.KLS.BKL.cumulantEnergy
          (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
          (r + 1) u :=
    FunctionalInequalities.KLS.BKL.Localization.sum_inner_noiseTensor_self μ hc p r u

  have hTL :
      FunctionalInequalities.Analysis.CoordinateTensor.inner T L =
        ∑ K : Fin r → Fin n,
          FunctionalInequalities.Analysis.BakryEmery.cumulant
              (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
              (r + 1)
              (Fin.cons u fun s =>
                FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p)
                  (EuclideanSpace.basisFun (Fin n) ℝ (K s))) *
            FunctionalInequalities.KLS.BKL.lowerDrift
              (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
              (Fin.cons u fun s =>
                FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p)
                  (EuclideanSpace.basisFun (Fin n) ℝ (K s))) 0 := by
    rfl

  have hg :
      FunctionalInequalities.KLS.BKL.Localization.generator μ hc
          (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n =>
            FunctionalInequalities.KLS.BKL.cumulantEnergy
              (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) r u) p =
        fderiv ℝ
            (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ×
              ((Fin r → Fin n) → ℝ) => FunctionalInequalities.Analysis.CoordinateTensor.energyForm q.1 q.2)
            (1, T) (-1, -(((r : ℝ) + 1) • T + L)) +
          (1 / 2 : ℝ) * ∑ i,
            fderiv ℝ
              (fderiv ℝ
                (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ×
                  ((Fin r → Fin n) → ℝ) => FunctionalInequalities.Analysis.CoordinateTensor.energyForm q.1 q.2))
              (1, T)
              (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseOperator μ hc p i, W i)
              (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseOperator μ hc p i, W i) :=
    FunctionalInequalities.KLS.BKL.Localization.generator_cumulantEnergy_eq_readable μ hc hiso hr u p

  have hformula :
      FunctionalInequalities.KLS.BKL.Localization.generator μ hc
          (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n =>
            FunctionalInequalities.KLS.BKL.cumulantEnergy
              (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) r u) p =
        -(((r : ℝ) + 1) + 1) * FunctionalInequalities.Analysis.CoordinateTensor.inner T T - 2 * FunctionalInequalities.Analysis.CoordinateTensor.inner T L
          + ∑ i, FunctionalInequalities.Analysis.CoordinateTensor.inner (W i) (W i)
          - 2 * ∑ i, FunctionalInequalities.Analysis.CoordinateTensor.inner (W i) (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T)
          + (1 / 2 : ℝ) * ∑ i,
              FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T) (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T)
          + (1 / 2 : ℝ) * ∑ i, ∑ s,
              FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn (H i) s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn (H i) s T) := by
    rw [hg, hfirst]
    simp_rw [hsecond]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring

  have hd :=
    FunctionalInequalities.Analysis.CoordinateTensor.drift_expression_ge_readable (r := r) (m := r + 1) rfl H hHerm h8' T L W
  rw [Nat.cast_add, Nat.cast_one] at hd
  rw [← hformula] at hd
  rw [hT, hW, hTL] at hd
  exact hd
