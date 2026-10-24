-- Prove2me | solution 1 for FunctionalInequalities.Analysis.inner_self_pos_of_isPositive_of_isUnit_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:43:22.446221+00:00
-- url     : https://prove2.me/submissions/2b8dedc3-f3a8-4831-9f0c-6cba1970e6c7

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.LinearAlgebra.Matrix.Kronecker

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
/-- The matrix is positive semidefinite iff the operator is positive (Mathlib `posSemidef_toMatrix_iff`). -/
theorem FunctionalInequalities.Analysis.operatorMatrix_posSemidef_iff (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    (operatorMatrix b T).PosSemidef ↔ T.IsPositive :=
  LinearMap.posSemidef_toMatrix_iff b
theorem FunctionalInequalities.Analysis.operatorMatrix_isUnit_iff (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    IsUnit (operatorMatrix b A) ↔ IsUnit A := by
  exact (LinearMap.isUnit_toMatrix_iff b.toBasis).trans
    ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.symm
/-- The quadratic form in coordinates. -/
theorem FunctionalInequalities.Analysis.inner_eq_dotProduct_operatorMatrix (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) (v : E) :
    ⟪v, T v⟫ = star (fun i => b.repr v i) ⬝ᵥ
      (operatorMatrix b T *ᵥ (fun i => b.repr v i)) := by
  have hm := T.toLinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis v
  have he (x : E) : (fun i => b.toBasis.repr x i) = (fun i => b.repr x i) :=
    funext (b.coe_toBasis_repr_apply x)
  change operatorMatrix b T *ᵥ (fun i => b.toBasis.repr v i) =
    (fun i => b.toBasis.repr (T v) i) at hm
  rw [he, he] at hm
  rw [hm, ← b.repr.inner_map_map v (T v)]
  change (fun i => b.repr (T v) i) ⬝ᵥ star (fun i => b.repr v i) = _
  exact dotProduct_comm _ _
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- A positive unit is strictly positive (converse of `isUnit_of_inner_self_pos`). -/
theorem solution (b : OrthonormalBasis ι ℝ E)
    (T : E →L[ℝ] E) (hpos : T.IsPositive) (hunit : IsUnit T)
    {v : E} (hv : v ≠ 0) : 0 < ⟪T v, v⟫ := by
  have hp := ((FunctionalInequalities.Analysis.operatorMatrix_posSemidef_iff b T).mpr hpos).posDef_iff_isUnit.mpr
    ((FunctionalInequalities.Analysis.operatorMatrix_isUnit_iff b T).mpr hunit)
  have hx : (fun i => b.repr v i) ≠ 0 := by
    intro hh
    apply hv
    apply b.repr.injective
    apply PiLp.ext
    intro i
    have := congrFun hh i
    simpa using this
  rw [real_inner_comm, FunctionalInequalities.Analysis.inner_eq_dotProduct_operatorMatrix b T v]
  exact hp.dotProduct_mulVec_pos hx
