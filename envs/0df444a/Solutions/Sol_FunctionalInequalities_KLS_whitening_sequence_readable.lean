-- Prove2me | solution 1 for FunctionalInequalities.KLS.whitening_sequence_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:36:10.026578+00:00
-- url     : https://prove2.me/submissions/8f5db320-810e-483f-93f5-f89022dd2051

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BallConditioning
import Theorems.Thm_FunctionalInequalities_Analysis_inverseSqrt_mul_mul_inverseSqrt_readable

section
noncomputable section
open scoped MatrixOrder Kronecker
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
section Frobenius
open Matrix Finset
open scoped RealInnerProductSpace
omit [Fintype ι] in
theorem FunctionalInequalities.Analysis.continuous_matrixEntries :
    Continuous (matrixEntries : Matrix ι ι ℝ → EuclideanSpace ℝ (ι × ι)) :=
  (PiLp.continuous_toLp 2 (fun _ : ι × ι => ℝ)).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))
end Frobenius
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
theorem FunctionalInequalities.Analysis.inverseSqrtIn_isUnit (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) : IsUnit (inverseSqrtIn b A) := by
  have hp : (operatorMatrix b A).PosDef :=
    ((operatorMatrix_posSemidef_iff b A).mpr hpos).posDef_iff_isUnit.mpr
      ((operatorMatrix_isUnit_iff b A).mpr hunit)
  apply (operatorMatrix_isUnit_iff b _).mp
  rw [operatorMatrix_inverseSqrtIn]
  exact (IsStrictlyPositive.sqrt _ hp.inv.isStrictlyPositive).isUnit
end
end
end

noncomputable section
open MeasureTheory Set Metric
open scoped RealInnerProductSpace ContDiff
section LT10BWhiteningMoments
open MeasureTheory Set Metric Filter
open scoped Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
 lemma solution (C : ℕ → E →L[ℝ] E)
    (hpos : ∀ k, (C k).IsPositive) (hC : Tendsto C atTop (𝓝 1)) :
    ∃ L : ℕ → E ≃L[ℝ] E,
      Tendsto (fun k => (L k).toContinuousLinearMap) atTop (𝓝 1) ∧
      ∀ᶠ k in atTop,
        IsSelfAdjoint (L k).toContinuousLinearMap ∧
        (L k).toContinuousLinearMap * C k * (L k).toContinuousLinearMap = 1 := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hu : ∀ᶠ k in atTop, IsUnit (C k) :=
    hC.eventually (Units.isOpen.mem_nhds isUnit_one)
  have hi0 : ContinuousAt Ring.inverse (1 : E →L[ℝ] E) :=
    NormedRing.inverse_continuousAt (1 : (E →L[ℝ] E)ˣ)
  have hi : Tendsto (fun k => Ring.inverse (C k)) atTop (𝓝 (1 : E →L[ℝ] E)) := by
    simpa only [Function.comp_def, Ring.inverse_one] using hi0.tendsto.comp hC
  have hmatrix : Continuous (FunctionalInequalities.Analysis.operatorMatrix b) :=
    ((LinearMap.toMatrixOrthonormal b).toAlgEquiv.toLinearMap.comp
      LinearMap.toContinuousLinearMap.symm.toLinearMap).continuous_of_finiteDimensional
  have hread : Continuous (FunctionalInequalities.Analysis.operatorOfMatrix b) := by
    simpa only [Function.comp_def, FunctionalInequalities.Analysis.operatorOfMatrixL_matrixEntries] using
      (FunctionalInequalities.Analysis.operatorOfMatrixL b).continuous.comp FunctionalInequalities.Analysis.continuous_matrixEntries
  have hmi :
      Tendsto (fun k => (FunctionalInequalities.Analysis.operatorMatrix b (C k))⁻¹) atTop
        (𝓝 (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)) := by
    have hh := (hmatrix.tendsto (1 : E →L[ℝ] E)).comp hi
    have he :
        (fun k => FunctionalInequalities.Analysis.operatorMatrix b (Ring.inverse (C k))) =ᶠ[atTop]
          (fun k => (FunctionalInequalities.Analysis.operatorMatrix b (C k))⁻¹) :=
      hu.mono fun k hk => (FunctionalInequalities.Analysis.operatorMatrix_ringInverse b (C k) hk).symm
    have hh' : Tendsto (fun k => FunctionalInequalities.Analysis.operatorMatrix b (Ring.inverse (C k)))
        atTop (𝓝 (FunctionalInequalities.Analysis.operatorMatrix b (1 : E →L[ℝ] E))) := hh
    simpa only [FunctionalInequalities.Analysis.operatorMatrix_one] using hh'.congr' he
  have hroot :
      Tendsto (fun k => CFC.sqrt ((FunctionalInequalities.Analysis.operatorMatrix b (C k))⁻¹))
        atTop
        (𝓝 (CFC.sqrt
          (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ))) := by
    have hs :
        ContinuousWithinAt
          (CFC.sqrt :
            Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ →
            Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
          {a | 0 ≤ a} 1 :=
      CFC.continuousOn_sqrt
        (A := Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
        1
        (show (0 : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) ≤ 1 from zero_le_one)
    apply hs.tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hmi, Eventually.of_forall fun k => ?_⟩
    exact ((FunctionalInequalities.Analysis.operatorMatrix_posSemidef_iff b (C k)).2 (hpos k)).inv.nonneg
  have hone : FunctionalInequalities.Analysis.operatorOfMatrix b
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) =
      (1 : E →L[ℝ] E) := by
    simpa only [FunctionalInequalities.Analysis.operatorMatrix_one] using
      FunctionalInequalities.Analysis.operatorOfMatrix_operatorMatrix b (1 : E →L[ℝ] E)
  have hW : Tendsto (fun k => FunctionalInequalities.Analysis.inverseSqrt (C k)) atTop (𝓝 1) := by
    have hh := (hread.tendsto _).comp hroot
    change Tendsto
      (fun k => FunctionalInequalities.Analysis.operatorOfMatrix b
        (CFC.sqrt ((FunctionalInequalities.Analysis.operatorMatrix b (C k))⁻¹))) atTop (𝓝 1)
    simpa only [Function.comp_def, CFC.sqrt_one, hone] using hh
  let L : ℕ → E ≃L[ℝ] E := fun k =>
    if hk : IsUnit (C k) then
      ContinuousLinearEquiv.ofUnit
        (FunctionalInequalities.Analysis.inverseSqrtIn_isUnit b (C k) (hpos k) hk).unit
    else ContinuousLinearEquiv.refl ℝ E
  have he :
      (fun k => (L k).toContinuousLinearMap) =ᶠ[atTop]
        (fun k => FunctionalInequalities.Analysis.inverseSqrt (C k)) := by
    filter_upwards [hu] with k hk
    dsimp only [L]
    rw [dif_pos hk]
    change
      (↑(FunctionalInequalities.Analysis.inverseSqrtIn_isUnit b (C k) (hpos k) hk).unit :
        E →L[ℝ] E) = FunctionalInequalities.Analysis.inverseSqrt (C k)
    exact (FunctionalInequalities.Analysis.inverseSqrtIn_isUnit b (C k) (hpos k) hk).unit_spec
  refine ⟨L, hW.congr' he.symm, ?_⟩
  filter_upwards [hu, he] with k hk heq
  rw [heq]
  exact ⟨FunctionalInequalities.Analysis.inverseSqrtIn_isSelfAdjoint b (C k),
    FunctionalInequalities.Analysis.inverseSqrt_mul_mul_inverseSqrt_readable (C k) (hpos k) hk⟩
