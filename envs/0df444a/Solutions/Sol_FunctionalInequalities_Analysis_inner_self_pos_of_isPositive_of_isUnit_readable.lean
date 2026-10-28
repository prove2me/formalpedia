-- Prove2me | solution 1 for FunctionalInequalities.Analysis.inner_self_pos_of_isPositive_of_isUnit_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:40:04.286525+00:00
-- url     : https://prove2.me/submissions/838baf4b-b9a0-45f4-b831-86d68e0e0961

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates

noncomputable section
open scoped RealInnerProductSpace MatrixOrder
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
