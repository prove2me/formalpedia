-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.exists_standardized_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:36:00.055453+00:00
-- url     : https://prove2.me/submissions/dc981300-77ec-46bc-90fa-156398f44929

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CompactReduction
import Theorems.Thm_FunctionalInequalities_Analysis_inverseSqrt_mul_mul_inverseSqrt_readable
import Theorems.Thm_FunctionalInequalities_Covariance_operator_map_continuousLinearEquiv_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_memLp_id_two_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_of_continuousLinearEquiv_map_readable

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
universe u v
section Translation
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (ν : MeasureTheory.ProbabilityMeasure V) (c : V)
variable [CompleteSpace V]
/-- Translation does not change the covariance operator. -/
theorem FunctionalInequalities.Covariance.operator_translateLaw :
    Covariance.operator (Probability.translateLaw ν c : Measure V) = Covariance.operator (ν : Measure V) := by
  unfold Covariance.operator
  rw [Probability.coe_translateLaw, ProbabilityTheory.covarianceBilin_map_const_add]
end Translation
end
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
open MeasureTheory Filter Topology InnerProductSpace
section
open FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean FunctionalInequalities.Probability
section Euclidean
variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
  [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
  [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂]
section
omit [CompleteSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] [CompleteSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂] in
/-- The image of a log-concave law under a continuous linear equivalence is log-concave. -/
theorem FunctionalInequalities.KLS.LogConcave.mapContinuousLinearEquiv {ν : ProbabilityMeasure V₁} (hν : LogConcave ν) (T : V₁ ≃L[ℝ] V₂) :
    LogConcave (Probability.mapContinuousLinearEquiv ν T) :=
  hν.of_continuousLinearEquiv_map_readable _ T.symm (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T).map_eq
end
section
omit [CompleteSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] in
omit [InnerProductSpace ℝ V₁] in
/-- Translation keeps a finite second moment. -/
theorem FunctionalInequalities.Probability.memLp_id_two_translateLaw
    (ν : ProbabilityMeasure V₁) (c : V₁) (h : MemLp id 2 (ν : Measure V₁)) :
    MemLp id 2 (translateLaw ν c : Measure V₁) := by
  rw [coe_translateLaw]
  exact (measurableEmbedding_addLeft c).memLp_map_measure_iff.mpr ((memLp_const c).add h)
end
end Euclidean
end
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
section S8CCompactToGeneral
open Filter Topology ProbabilityTheory FunctionalInequalities.Analysis
section MeasureHelpers
variable {E : Type*} [NormedAddCommGroup E]
section InnerProduct
variable [InnerProductSpace ℝ E]
/-- **Standardisation of a compactly supported log-concave law** with positive invertible covariance: the
law of `σ (x - a)`, with `σ = Cov^{-1/2}` and `a` the mean, is isotropic, log-concave and compactly
supported. -/
theorem solution [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ProbabilityMeasure E) (hLC : FunctionalInequalities.KLS.LogConcave μ)
    (hc : IsCompact (μ : Measure E).support)
    (hpos : (FunctionalInequalities.Covariance.operator (μ : Measure E)).IsPositive)
    (hunit : IsUnit (FunctionalInequalities.Covariance.operator (μ : Measure E))) :
    ∃ (η : ProbabilityMeasure E) (W : E ≃L[ℝ] E),
      (W : E →L[ℝ] E) = FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator (μ : Measure E)) ∧
      FunctionalInequalities.KLS.Isotropic η ∧ FunctionalInequalities.KLS.LogConcave η ∧ IsCompact (η : Measure E).support ∧
      (η : Measure E) = (μ : Measure E).map (fun x => W (x - ∫ y, y ∂(μ : Measure E))) := by
  let A : E →L[ℝ] E := FunctionalInequalities.Covariance.operator (μ : Measure E)
  let σ : E →L[ℝ] E := FunctionalInequalities.Analysis.inverseSqrt A
  have hσ : IsUnit σ := by
    change IsUnit (FunctionalInequalities.Analysis.inverseSqrtIn (stdOrthonormalBasis ℝ E) A)
    exact FunctionalInequalities.Analysis.inverseSqrtIn_isUnit (stdOrthonormalBasis ℝ E) A hpos hunit
  let W : E ≃L[ℝ] E := ContinuousLinearEquiv.ofUnit hσ.unit
  have hW : (W : E →L[ℝ] E) = σ := by
    change (↑hσ.unit : E →L[ℝ] E) = σ
    exact hσ.unit_spec
  have hWx : ∀ x, W x = σ x := fun x => by rw [← hW]; rfl
  let a : E := ∫ y, y ∂(μ : Measure E)
  let ν' : ProbabilityMeasure E := FunctionalInequalities.Probability.translateLaw μ (-a)
  let η : ProbabilityMeasure E := FunctionalInequalities.Probability.mapContinuousLinearEquiv ν' W
  have hηcoe : (η : Measure E) = (ν' : Measure E).map W := rfl
  have hmeas : Measurable fun x : E => W (x - a) :=
    (W.continuous.comp (continuous_id.sub continuous_const)).measurable
  have hmap : (η : Measure E) = (μ : Measure E).map (fun x => W (x - a)) := by
    rw [hηcoe, FunctionalInequalities.Probability.coe_translateLaw,
      Measure.map_map W.continuous.measurable (measurable_const_add (-a))]
    congr 1
    funext x
    simp [neg_add_eq_sub]
  have hμlp : MemLp id 2 (μ : Measure E) := hLC.memLp_id_two_readable
  have hint : Integrable id (μ : Measure E) := hμlp.integrable (by norm_num)
  have ht : MemLp id 2 (ν' : Measure E) := FunctionalInequalities.Probability.memLp_id_two_translateLaw μ (-a) hμlp
  have hηlp : MemLp id 2 (η : Measure E) := by
    rw [hηcoe, memLp_map_measure_iff measurable_id.aestronglyMeasurable W.continuous.aemeasurable]
    simpa [Function.comp_def] using (W : E →L[ℝ] E).comp_memLp' ht
  have hzero : ∫ x, x ∂(ν' : Measure E) = 0 :=
    FunctionalInequalities.Probability.integral_id_translateLaw_neg_integral μ hint
  have hmean : ∫ x, x ∂(η : Measure E) = 0 := by
    rw [hηcoe]
    change ∫ x, id x ∂((ν' : Measure E).map W) = 0
    rw [integral_map W.continuous.aemeasurable hηlp.aestronglyMeasurable]
    simp only [id_eq]
    rw [W.integral_comp_comm]
    simpa using congrArg W hzero
  have hself : (σ.adjoint : E →L[ℝ] E) = σ := (FunctionalInequalities.Analysis.inverseSqrt_spec A hpos hunit).2.1.adjoint_eq
  have halg : (σ.comp A).comp σ = 1 := by
    ext x
    simpa [σ, ContinuousLinearMap.comp_apply] using
      congrArg (fun T : E →L[ℝ] E => T x) (FunctionalInequalities.Analysis.inverseSqrt_mul_mul_inverseSqrt_readable A hpos hunit)
  have hiso : FunctionalInequalities.KLS.Isotropic η := by
    refine ⟨hηlp, hmean, ?_⟩
    rw [hηcoe, FunctionalInequalities.Covariance.operator_map_continuousLinearEquiv_readable, FunctionalInequalities.Covariance.operator_translateLaw, hW,
      hself]
    exact halg
  have hLCη : FunctionalInequalities.KLS.LogConcave η := (hLC.translateLaw (-a)).mapContinuousLinearEquiv W
  have hcη : IsCompact (η : Measure E).support := by
    have hK : IsCompact ((fun x : E => W (x - a)) '' (μ : Measure E).support) :=
      hc.image (W.continuous.comp (continuous_id.sub continuous_const))
    refine hK.of_isClosed_subset Measure.isClosed_support
      (Measure.support_subset_of_isClosed hK.isClosed ?_)
    have hinj : Function.Injective fun x : E => W (x - a) := fun x y hxy =>
      sub_left_injective (W.injective hxy)
    rw [mem_ae_iff, hmap, Measure.map_apply hmeas hK.isClosed.measurableSet.compl,
      Set.preimage_compl, Set.preimage_image_eq _ hinj]
    exact Measure.measure_compl_support
  exact ⟨η, W, hW, hiso, hLCη, hcη, hmap⟩
