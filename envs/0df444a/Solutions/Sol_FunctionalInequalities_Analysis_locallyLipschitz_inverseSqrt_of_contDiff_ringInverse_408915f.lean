-- Prove2me | solution 1 for FunctionalInequalities.Analysis.locallyLipschitz_inverseSqrt_of_contDiff_ringInverse_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:48:39.787955+00:00
-- url     : https://prove2.me/submissions/3879825b-addb-4766-96ab-de11842ab0cb

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
import Theorems.Thm_FunctionalInequalities_Analysis_locallyLipschitz_matrixEntries_sqrt_408915f

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
section LocalLipschitz
open Matrix Set Filter Topology
open scoped Matrix.Norms.L2Operator NNReal ContDiff
/-- The same, with the root read back as an operator in the operator norm. -/
theorem FunctionalInequalities.Analysis.locallyLipschitz_operatorOfMatrix_sqrt {X : Type*} [PseudoMetricSpace X]
    (b : OrthonormalBasis ι ℝ E) (M : X → Matrix ι ι ℝ)
    (hM : Continuous M) (hPD : ∀ x, (M x).PosDef)
    (hInput : LocallyLipschitz (fun x => matrixEntries (M x))) :
    LocallyLipschitz (fun x => operatorOfMatrix b (CFC.sqrt (M x))) := by
  have h := (operatorOfMatrixL b).lipschitz.locallyLipschitz.comp
    (locallyLipschitz_matrixEntries_sqrt_408915f M hM hPD hInput)
  simpa only [Function.comp_def, operatorOfMatrixL_matrixEntries] using h
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Local Lipschitz property of the principal inverse square root** along an operator profile `A` on a
normed parameter space: if `Ring.inverse ∘ A` is `C¹` with positive values and every `A p` is a unit, then
`p ↦ inverseSqrt (A p)` is locally Lipschitz in the operator norm. -/
theorem solution {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] (A : P → (E →L[ℝ] E))
    (hpos : ∀ p, (Ring.inverse (A p)).IsPositive)
    (hunit : ∀ p, IsUnit (A p))
    (hInverse : ContDiff ℝ 1 (fun p => Ring.inverse (A p))) :
    LocallyLipschitz (fun p => FunctionalInequalities.Analysis.inverseSqrt (A p)) := by
  let b := stdOrthonormalBasis ℝ E
  let M := fun p => FunctionalInequalities.Analysis.operatorMatrix b (Ring.inverse (A p))
  have hChart : ContDiff ℝ 1 (fun p => FunctionalInequalities.Analysis.matrixEntries (M p)) := by
    simpa only [Function.comp_def, FunctionalInequalities.Analysis.operatorMatrixL_apply] using
      (FunctionalInequalities.Analysis.operatorMatrixL b).contDiff.comp hInverse
  have hPD : ∀ p, (M p).PosDef := by
    intro p
    apply ((FunctionalInequalities.Analysis.operatorMatrix_posSemidef_iff b _).mpr (hpos p)).posDef_iff_isUnit.mpr
    apply (FunctionalInequalities.Analysis.operatorMatrix_isUnit_iff b _).mpr
    exact (hunit p).ringInverse
  have hM : Continuous M := by
    exact (((LinearMap.toMatrixOrthonormal b).toAlgEquiv.toLinearMap.comp
      LinearMap.toContinuousLinearMap.symm.toLinearMap).toContinuousLinearMap).continuous.comp
      hInverse.continuous
  have h := FunctionalInequalities.Analysis.locallyLipschitz_operatorOfMatrix_sqrt b M hM hPD hChart.locallyLipschitz
  have heq : (fun p => FunctionalInequalities.Analysis.operatorOfMatrix b (CFC.sqrt (M p))) = (fun p => FunctionalInequalities.Analysis.inverseSqrt (A p)) := by
    funext p
    unfold FunctionalInequalities.Analysis.inverseSqrt FunctionalInequalities.Analysis.inverseSqrtIn
    rw [FunctionalInequalities.Analysis.operatorMatrix_ringInverse _ _ (hunit p)]
  rwa [heq] at h
