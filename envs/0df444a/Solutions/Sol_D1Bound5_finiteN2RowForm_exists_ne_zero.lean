-- Prove2me | solution 1 for D1Bound5.finiteN2RowForm_exists_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:12.870705+00:00
-- url     : https://prove2.me/submissions/8b4683f8-c409-4e33-a0d2-de1b619837ef

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
import Definitions.Def_D1Bound5_FiniteN2IntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions

section
namespace D1Bound5

variable {R : Type*} [CommRing R]



















set_option maxHeartbeats 1000000 in
/-- The determinant is verified from the actual integer polynomials.
The manuscript's constant -1800 is divided by g^3=8. -/
theorem finiteN2DividedMatrix_det (x y c : R) :
    (finiteN2DividedMatrix x y c).det = -225*(x-y)^7 := by
  simp [finiteN2DividedMatrix, finiteN2Constant, finiteN2Left, finiteN2Right,
    Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix]
  <;> ring



theorem finiteN2DividedMatrix_det_ne_zero
    {F : Type*} [Field F] [CharZero F] (x y c : F) (hxy : x ≠ y) :
    (finiteN2DividedMatrix x y c).det ≠ 0 := by
  rw [finiteN2DividedMatrix_det]
  norm_num [mul_eq_zero, sub_eq_zero, hxy]

end D1Bound5
end

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]













theorem _root_.solution
    {F : Type*} [Field F] [CharZero F]
    (x y c z sX sY : F) (hxy : x ≠ y) (hz : z ≠ 0) :
    ∃ i : Fin 3, finiteN2RowForm x y c z sX sY i ≠ 0 := by
  classical
  let Q := finiteN2DividedMatrix x y c
  let v : Fin 3 → F := ![z,sX,sY]
  have hdet : Q.det ≠ 0 := finiteN2DividedMatrix_det_ne_zero x y c hxy
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
