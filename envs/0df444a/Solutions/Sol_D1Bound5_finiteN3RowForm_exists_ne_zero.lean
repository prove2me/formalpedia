-- Prove2me | solution 1 for D1Bound5.finiteN3RowForm_exists_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:48:05.911955+00:00
-- url     : https://prove2.me/submissions/fd39e2c1-a5f8-4e3b-b23b-c5e63c909286

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteN3IntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteN3Matrix_Definitions

section
namespace D1Bound5

variable {R : Type*} [CommRing R]



















set_option maxHeartbeats 4000000 in
/-- The determinant is verified from the actual integer polynomials.
The manuscript's constant235200 is divided by g^3=64. -/
theorem finiteN3DividedMatrix_det (x y c : R) :
    (finiteN3DividedMatrix x y c).det = 3675*x*y*(x-y)^11 := by
  simp [finiteN3DividedMatrix, finiteN3Constant, finiteN3Left, finiteN3Right,
    Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix]
  <;> ring



theorem finiteN3DividedMatrix_det_ne_zero
    {F : Type*} [Field F] [CharZero F] (x y c : F) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    (finiteN3DividedMatrix x y c).det ≠ 0 := by
  rw [finiteN3DividedMatrix_det]
  norm_num [mul_eq_zero, sub_eq_zero, hx, hy, hxy]

end D1Bound5
end

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]













theorem _root_.solution
    {F : Type*} [Field F] [CharZero F]
    (x y c z sX sY : F) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) (hz : z ≠ 0) :
    ∃ i : Fin 3, finiteN3RowForm x y c z sX sY i ≠ 0 := by
  classical
  let Q := finiteN3DividedMatrix x y c
  let v : Fin 3 → F := ![z,sX,sY]
  have hdet : Q.det ≠ 0 := finiteN3DividedMatrix_det_ne_zero x y c hx hy hxy
  have hunit : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).2
    (isUnit_iff_ne_zero.mpr hdet)
  have hinj : Function.Injective Q.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hunit
  by_contra h
  push_neg at h
  have hzero : Q.mulVec v = 0 := by funext i; exact h i
  have hv : v = 0 := hinj (by simpa using hzero)
  exact hz (by simpa [v] using congrFun hv (0 : Fin 3))



end D1Bound5
end
