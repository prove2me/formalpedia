-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.generator_logLaplace_posterior_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:39:00.385982+00:00
-- url     : https://prove2.me/submissions/2338dbec-2009-4623-9ac6-268ea7e872bd

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
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator
import Theorems.Thm_FunctionalInequalities_Analysis_inner_self_pos_of_isPositive_of_isUnit_readable
import Theorems.Thm_FunctionalInequalities_Covariance_inner_operator_self_pos_of_affineSupport_eq_top_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_fderiv_logLaplace_fst_dir_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_posteriorExpectation_exp_inner_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_posteriorExpectation_exp_inner_eq_exp_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_sum_inner_inverseSqrt_sq_readable
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_diffusionGenerator_comp_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_logPartition_joint_readable

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

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
open scoped ContDiff
section ExpDeriv
theorem FunctionalInequalities.KLS.BKL.Localization.fderiv_exp_apply' (t u : ℝ) : fderiv ℝ Real.exp t u = Real.exp t * u := by
  rw [(Real.hasDerivAt_exp t).hasFDerivAt.fderiv]
  simp [mul_comm]
theorem FunctionalInequalities.KLS.BKL.Localization.fderiv_fderiv_exp_apply (t u v : ℝ) :
    fderiv ℝ (fderiv ℝ Real.exp) t u v = Real.exp t * u * v := by
  have h2 : fderiv ℝ Real.exp = fun s => Real.exp s • (1 : ℝ →L[ℝ] ℝ) := by
    funext s
    refine ContinuousLinearMap.ext fun w => ?_
    rw [fderiv_exp_apply']
    simp
  have h3 : HasFDerivAt (fun s => Real.exp s • (1 : ℝ →L[ℝ] ℝ))
      ((fderiv ℝ Real.exp t).smulRight (1 : ℝ →L[ℝ] ℝ)) t :=
    Real.differentiableAt_exp.hasFDerivAt.smul_const (1 : ℝ →L[ℝ] ℝ)
  rw [h2, h3.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, one_apply_eq_self, smul_eq_mul]
  rw [fderiv_exp_apply']
end ExpDeriv
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
/-- Self-adjointness and the square identity of the diffusion coefficient `σ = A(p)^{-1/2}`. -/
theorem FunctionalInequalities.KLS.BKL.Localization.inverseSqrt_cov_props (hiso : KLS.Isotropic μ) (p : Param n) :
    (∀ u v, ⟪inverseSqrt (cov μ hc p) u, v⟫ = ⟪u, inverseSqrt (cov μ hc p) v⟫) ∧
      ∀ v, inverseSqrt (cov μ hc p) (inverseSqrt (cov μ hc p) v) = Ring.inverse (cov μ hc p) v := by
  have hspec := Isotropic.compactPosterior_inverseSqrt_spec μ hc hiso p.1 p.2
  dsimp only at hspec
  obtain ⟨hsa, -, -, hsq, -, -, -⟩ := hspec
  refine ⟨fun u v => ?_, fun v => ?_⟩
  · exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) u v
  · change (inverseSqrt (cov μ hc p) * inverseSqrt (cov μ hc p)) v = _
    exact congrArg (fun T => T v) hsq
include hc in
/-- Joint smoothness of the log-Laplace transform `Λ(q) = ψ(q.1 + z, q.2) − ψ(q.1, q.2)`. -/
theorem FunctionalInequalities.KLS.BKL.Localization.contDiff_logLaplace_joint (z : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞
      (fun q : Param n => logPartition μ (q.1 + z) q.2 - logPartition μ q.1 q.2) := by
  have hjoint := contDiff_logPartition_joint_readable μ hc
  have hmap : ContDiff ℝ ∞ (fun q : Param n => ((q.1 + z, q.2) : Param n)) :=
    (contDiff_fst.add contDiff_const).prodMk contDiff_snd
  have h1 := hjoint.comp hmap
  have h1' : ContDiff ℝ ∞ (fun q : Param n => logPartition μ (q.1 + z) q.2) := by
    convert h1 using 1
    rfl
  exact h1'.sub hjoint
/-- **BKL (71) in generator form**: for every `z`, the generator of (67) applied to the log-Laplace
transform of the posterior, `Λ_p(z) = ψ(c + z, Q) − ψ(c, Q)`, is `−½ ⟪v, A⁻¹ v⟫` with
`v = a(c + z, Q) − a(c, Q)` (the drift of `dΛ_t(z)` in (71)); every parameter `p`, isotropic compact prior. -/
theorem solution (hiso : FunctionalInequalities.KLS.Isotropic μ) (z : EuclideanSpace ℝ (Fin n))
    (p : FunctionalInequalities.KLS.BKL.Localization.Param n) :
    FunctionalInequalities.KLS.BKL.Localization.generator μ hc (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Probability.Posterior.logPartition μ (q.1 + z) q.2 - FunctionalInequalities.Probability.Posterior.logPartition μ q.1 q.2) p =
      -(1 / 2 : ℝ) * ⟪FunctionalInequalities.Probability.Posterior.posteriorMean μ (p.1 + z) p.2 - FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2,
        Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p) (FunctionalInequalities.Probability.Posterior.posteriorMean μ (p.1 + z) p.2 - FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2)⟫ := by
  obtain ⟨hσ, hM⟩ := FunctionalInequalities.KLS.BKL.Localization.inverseSqrt_cov_props μ hc hiso p
  set Λ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ := fun q => FunctionalInequalities.Probability.Posterior.logPartition μ (q.1 + z) q.2 - FunctionalInequalities.Probability.Posterior.logPartition μ q.1 q.2 with hΛdef
  set v := FunctionalInequalities.Probability.Posterior.posteriorMean μ (p.1 + z) p.2 - FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2 with hvdef
  have hΛ : ContDiff ℝ ∞ Λ := FunctionalInequalities.KLS.BKL.Localization.contDiff_logLaplace_joint μ hc z
  have hΛ2 : ContDiff ℝ 2 Λ := hΛ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hF : (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ q.1 q.2 (fun x => Real.exp ⟪z, x⟫)) =
      Real.exp ∘ Λ := by
    funext q
    exact FunctionalInequalities.KLS.BKL.Localization.posteriorExpectation_exp_inner_eq_exp_readable μ hc z q
  have hzero := FunctionalInequalities.KLS.BKL.Localization.generator_posteriorExpectation_exp_inner_readable μ hc hiso z p
  rw [hF] at hzero
  unfold FunctionalInequalities.KLS.BKL.Localization.generator at hzero
  rw [FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp_readable _ _ Real.exp Λ p Real.contDiff_exp hΛ2] at hzero
  simp only [FunctionalInequalities.KLS.BKL.Localization.fderiv_exp_apply', FunctionalInequalities.KLS.BKL.Localization.fderiv_fderiv_exp_apply, smul_eq_mul] at hzero
  have hd : ∀ k, fderiv ℝ Λ p (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k) =
      ⟪FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p) (EuclideanSpace.single k 1), v⟫ := by
    intro k
    exact FunctionalInequalities.KLS.BKL.Localization.fderiv_logLaplace_fst_dir_readable μ hc z p _
  have hsum : ∑ k, fderiv ℝ Λ p (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k) * fderiv ℝ Λ p (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k) =
      ⟪v, Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p) v⟫ := by
    simp only [hd]
    rw [FunctionalInequalities.KLS.BKL.Localization.sum_inner_inverseSqrt_sq_readable _ hσ v, hM]
  have hS : ∑ k, Real.exp (Λ p) * fderiv ℝ Λ p (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k) * fderiv ℝ Λ p (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k) =
      Real.exp (Λ p) * ⟪v, Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p) v⟫ := by
    rw [← hsum, Finset.mul_sum]
    simp only [mul_assoc]
  rw [hS] at hzero
  have hexp : Real.exp (Λ p) ≠ 0 := (Real.exp_pos _).ne'
  unfold FunctionalInequalities.KLS.BKL.Localization.generator FunctionalInequalities.Probability.Diffusion.diffusionGenerator
  apply mul_left_cancel₀ hexp
  linear_combination hzero
