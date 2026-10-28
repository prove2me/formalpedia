-- Prove2me | solution 1 for FunctionalInequalities.KLS.compactPosterior_cumulant_bound_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:32:06.199817+00:00
-- url     : https://prove2.me/submissions/86ed3f2a-b870-4b43-9ccd-b381ebea7ba8

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
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Standardization
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cumulant_map_affine_readable
import Theorems.Thm_FunctionalInequalities_Analysis_inverseSqrt_mul_mul_inverseSqrt_readable
import Theorems.Thm_FunctionalInequalities_Covariance_inner_operator_self_pos_of_affineSupport_eq_top_readable
import Theorems.Thm_FunctionalInequalities_KLS_Isotropic_exists_inverseSqrt_equiv_isotropic_standardized_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_logConcave_of_concave_tilt_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_of_continuousLinearEquiv_map_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_quadraticExponent_concave_readable

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
/-- **The BKL posterior of a log-concave compact prior is log-concave for `Q ≥ 0`** (p. 19: "each `μ_t` is
log-concave since `Q_t ≥ 0`"); singular priors, `Q = 0`, any `c` and rank zero included. -/
theorem FunctionalInequalities.KLS.compactPosterior_logConcave (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hLC : KLS.LogConcave μ)
    (c : E) (Q : E →L[ℝ] E) (hSym : IsSelfAdjoint Q)
    (hQ : ∀ x : E, 0 ≤ ⟪Q x, x⟫) : KLS.LogConcave (compactPosterior μ hc c Q) := by
  apply LogConcave.logConcave_of_concave_tilt_readable μ (compactPosterior μ hc c Q) hLC (quadraticExponent c Q)
    (by unfold quadraticExponent; fun_prop)
  · exact Probability.Posterior.quadraticExponent_concave_readable c Q
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hSym) hQ
  · rfl
/-- The posterior covariance is a positive operator. -/
theorem FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_isPositive (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    (Covariance.operator (compactPosterior μ hc c Q : Measure E)).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff' _).mpr
  refine ⟨Covariance.operator_isSelfAdjoint _, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · exact (Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hv).le
variable {ι : Type*} [Fintype ι]
end
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
/-- **Standardized posterior cumulant bound** (BKL arXiv:2610.05474v1, (77)): for a compactly supported
isotropic log-concave prior and a posterior with symmetric positive semidefinite `Q`, a cumulant bound
`CumulantBoundCompact d b` (`d ≥ 1`) applied to the standardized posterior
`ν = (A^{-1/2}(· − a))_* μ_{c,Q}` gives, with `σ = A^{-1/2}`,
`Σ_J κ_{d+1}(μ_{c,Q})(v, σ e_{J_1}, …, σ e_{J_d})² ≤ b ⟪A v, v⟫`, i.e. `‖κ_{d+1}(t)(v)‖²_t ≤ b ⟨A_t v, v⟩`. -/
theorem solution {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hiso : FunctionalInequalities.KLS.Isotropic μ) (hLC : FunctionalInequalities.KLS.LogConcave μ)
    (c : EuclideanSpace ℝ (Fin n)) (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hSym : IsSelfAdjoint Q) (hQ : ∀ x, 0 ≤ ⟪Q x, x⟫)
    {d : ℕ} (hd : 1 ≤ d) {b : ℝ} (h : FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBoundCompact d b)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∑ J : Fin d → Fin n,
        FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
          (Fin.cons v fun k => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator
            (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
              (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^ 2 ≤
      b * ⟪FunctionalInequalities.Covariance.operator (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫ := by
  let π : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := FunctionalInequalities.Probability.Posterior.compactPosterior μ hc c Q
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    FunctionalInequalities.Covariance.operator (π : Measure (EuclideanSpace ℝ (Fin n)))
  let σ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := FunctionalInequalities.Analysis.inverseSqrt A
  let a : EuclideanSpace ℝ (Fin n) := FunctionalInequalities.Probability.Posterior.posteriorMean μ c Q
  let η : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
    FunctionalInequalities.Probability.translateLaw π (-a)
  obtain ⟨W, hW, hνiso⟩ :=
    FunctionalInequalities.KLS.Isotropic.exists_inverseSqrt_equiv_isotropic_standardized_readable μ hc hiso c Q
  let ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
    FunctionalInequalities.Probability.mapContinuousLinearEquiv η W
  have hW' : (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = σ := by
    simpa [π, A, σ] using hW
  have hpos : A.IsPositive := by
    simpa [π, A] using
      FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_isPositive μ hc hiso c Q
  have hunit : IsUnit A := by
    simpa [π, A] using
      FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_isUnit μ hc hiso c Q
  have hself :
      ContinuousLinearMap.adjoint σ = σ := by
    change ContinuousLinearMap.adjoint (FunctionalInequalities.Analysis.inverseSqrt A) = FunctionalInequalities.Analysis.inverseSqrt A
    exact (FunctionalInequalities.Analysis.inverseSqrt_spec A hpos hunit).2.1
  have halg : (σ.comp A).comp σ = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    change σ (A (σ x)) = x
    simpa [σ] using
      congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => T x)
        (FunctionalInequalities.Analysis.inverseSqrt_mul_mul_inverseSqrt_readable A hpos hunit)
  have hνcoe :
      (ν : Measure (EuclideanSpace ℝ (Fin n))) =
        Measure.map (fun x => W (x - a)) (π : Measure (EuclideanSpace ℝ (Fin n))) := by
    change
      (FunctionalInequalities.Probability.mapContinuousLinearEquiv η W :
        Measure (EuclideanSpace ℝ (Fin n))) =
        Measure.map (fun x => W (x - a)) (π : Measure (EuclideanSpace ℝ (Fin n)))
    rw [FunctionalInequalities.Probability.coe_mapContinuousLinearEquiv, FunctionalInequalities.Probability.coe_translateLaw,
      Measure.map_map W.continuous.measurable (measurable_const_add _)]
    congr 1
    funext x
    simp [sub_eq_add_neg, add_comm]
  have hπLC : FunctionalInequalities.KLS.LogConcave π := by
    simpa [π] using FunctionalInequalities.KLS.compactPosterior_logConcave μ hc hLC c Q hSym hQ
  have hηLC : FunctionalInequalities.KLS.LogConcave η := by
    simpa [η] using hπLC.translateLaw (-a)
  have hmapback :
      Measure.map (W.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          (ν : Measure (EuclideanSpace ℝ (Fin n))) =
        (η : Measure (EuclideanSpace ℝ (Fin n))) :=
    (FunctionalInequalities.Probability.measurePreserving_mapContinuousLinearEquiv_symm η W).map_eq
  have hνLC : FunctionalInequalities.KLS.LogConcave ν :=
    FunctionalInequalities.KLS.LogConcave.of_continuousLinearEquiv_map_readable hηLC ν W.symm hmapback
  have hπcompact : IsCompact (π : Measure (EuclideanSpace ℝ (Fin n))).support := by
    change IsCompact (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))).support
    rw [FunctionalInequalities.Probability.Posterior.compactPosterior_support μ hc c Q]
    exact hc
  let K : Set (EuclideanSpace ℝ (Fin n)) :=
    (fun x => W (x - a)) '' (π : Measure (EuclideanSpace ℝ (Fin n))).support
  have hKcompact : IsCompact K := by
    apply hπcompact.image
    exact W.continuous.comp (continuous_id.sub continuous_const)
  have hKae : K ∈ ae (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [hνcoe]
    apply
      (ae_map_iff
        (W.continuous.comp (continuous_id.sub continuous_const)).aemeasurable
        hKcompact.measurableSet).2
    filter_upwards [Measure.support_mem_ae
      (μ := (π : Measure (EuclideanSpace ℝ (Fin n))))] with x hx
    exact ⟨x, hx, rfl⟩
  have hνcompact :
      IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support := by
    apply IsCompact.of_isClosed_subset hKcompact
    · exact Measure.isClosed_support
    · exact Measure.support_subset_of_isClosed hKcompact.isClosed hKae
  have hexp (r : ℝ) :
      Integrable
        (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (r * ‖x‖))
        (π : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply FunctionalInequalities.Probability.Posterior.integrable_exp_of_compact π hπcompact
    fun_prop
  have hk : 2 ≤ d + 1 := by omega
  have hcum (J : Fin d → Fin n) :
      FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
          (Fin.cons (W.symm v) fun k =>
            EuclideanSpace.basisFun (Fin n) ℝ (J k)) =
        FunctionalInequalities.Analysis.BakryEmery.cumulant (π : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
          (Fin.cons v fun k =>
            σ (EuclideanSpace.basisFun (Fin n) ℝ (J k))) := by
    rw [hνcoe, FunctionalInequalities.Analysis.BakryEmery.cumulant_map_affine_readable W a (π : Measure (EuclideanSpace ℝ (Fin n))) hexp hk]
    have hWadj :
        ContinuousLinearMap.adjoint
            (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = σ := by
      rw [hW', hself]
    congr 1
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [Fin.cons_zero, hWadj]
      rw [← hW']
      exact W.apply_symm_apply v
    · simp only [Fin.cons_succ, hWadj]
  have hsum :
      ∑ J : Fin d → Fin n,
          FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
            (Fin.cons (W.symm v) fun k =>
              EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 =
        ∑ J : Fin d → Fin n,
          FunctionalInequalities.Analysis.BakryEmery.cumulant (π : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
            (Fin.cons v fun k =>
              σ (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^ 2 := by
    apply Finset.sum_congr rfl
    intro J hJ
    rw [hcum]
  have hnorm :
      ‖W.symm v‖ ^ 2 =
        ⟪A v, v⟫ := by
    let u := W.symm v
    have hv : v = σ u := by
      dsimp [u]
      rw [← hW']
      exact (W.apply_symm_apply v).symm
    have hu : σ (A (σ u)) = u := by
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => T u)
          halg
    calc
      ‖u‖ ^ 2 = ⟪u, u⟫ := (real_inner_self_eq_norm_sq u).symm
      _ = ⟪σ (A (σ u)), u⟫ := by rw [hu]
      _ = ⟪A (σ u), (ContinuousLinearMap.adjoint σ) u⟫ :=
        (ContinuousLinearMap.adjoint_inner_right σ (A (σ u)) u).symm
      _ = ⟪A (σ u), σ u⟫ := by rw [hself]
      _ = ⟪A v, v⟫ := by rw [← hv]
  have hbound :=
    h n ν hνiso hνLC hνcompact (W.symm v)
  calc
    ∑ J : Fin d → Fin n,
        FunctionalInequalities.Analysis.BakryEmery.cumulant (π : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
          (Fin.cons v fun k =>
            σ (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^ 2 =
        ∑ J : Fin d → Fin n,
          FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
            (Fin.cons (W.symm v) fun k =>
              EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 := hsum.symm
    _ ≤ b * ‖W.symm v‖ ^ 2 := hbound
    _ = b * ⟪A v, v⟫ := by rw [hnorm]
    _ = b * ⟪FunctionalInequalities.Covariance.operator
          (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫ := by
      rfl
