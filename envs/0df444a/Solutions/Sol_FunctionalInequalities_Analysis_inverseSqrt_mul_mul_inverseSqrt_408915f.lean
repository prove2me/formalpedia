-- Prove2me | solution 1 for FunctionalInequalities.Analysis.inverseSqrt_mul_mul_inverseSqrt_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:45:06.39292+00:00
-- url     : https://prove2.me/submissions/df4fb9a5-a2b5-41e1-aff9-5bf53405a95b

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.LinearAlgebra.Matrix.Kronecker

section
noncomputable section
open scoped RealInnerProductSpace MatrixOrder
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
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
end

noncomputable section
open scoped MatrixOrder RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
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
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Root sandwich** `σ A σ = 1` for a positive unit `A` and `σ = inverseSqrt A`: from `A σσ = 1` and `σ` a unit,
`(σ A σ) σ = σ`, so `σ A σ = 1` (no commutation of `σ` with `A` is used).
-/
theorem solution (A : E →L[ℝ] E) (hpos : A.IsPositive) (hunit : IsUnit A) :
    FunctionalInequalities.Analysis.inverseSqrt A * A * FunctionalInequalities.Analysis.inverseSqrt A = 1 := by
    have hspec := FunctionalInequalities.Analysis.inverseSqrt_spec A hpos hunit
    have hsa : IsSelfAdjoint (FunctionalInequalities.Analysis.inverseSqrt A) := by
      aesop
    have hlraw :
        A * (FunctionalInequalities.Analysis.inverseSqrt A * (FunctionalInequalities.Analysis.inverseSqrt A).adjoint) = 1 := by
      aesop
    have hl : A * (FunctionalInequalities.Analysis.inverseSqrt A * FunctionalInequalities.Analysis.inverseSqrt A) = 1 := by
      simpa only [hsa.adjoint_eq] using hlraw
    have hσ : IsUnit (FunctionalInequalities.Analysis.inverseSqrt A) := by
      change IsUnit (FunctionalInequalities.Analysis.inverseSqrtIn (stdOrthonormalBasis ℝ E) A)
      exact FunctionalInequalities.Analysis.inverseSqrtIn_isUnit (stdOrthonormalBasis ℝ E) A hpos hunit
    have heq :
        (FunctionalInequalities.Analysis.inverseSqrt A * A * FunctionalInequalities.Analysis.inverseSqrt A) * FunctionalInequalities.Analysis.inverseSqrt A =
          1 * FunctionalInequalities.Analysis.inverseSqrt A := by
      calc
        (FunctionalInequalities.Analysis.inverseSqrt A * A * FunctionalInequalities.Analysis.inverseSqrt A) * FunctionalInequalities.Analysis.inverseSqrt A =
            FunctionalInequalities.Analysis.inverseSqrt A * (A * (FunctionalInequalities.Analysis.inverseSqrt A * FunctionalInequalities.Analysis.inverseSqrt A)) := by
              simp only [mul_assoc]
        _ = FunctionalInequalities.Analysis.inverseSqrt A * 1 := by rw [hl]
        _ = 1 * FunctionalInequalities.Analysis.inverseSqrt A := by simp
    exact hσ.mul_right_cancel heq
