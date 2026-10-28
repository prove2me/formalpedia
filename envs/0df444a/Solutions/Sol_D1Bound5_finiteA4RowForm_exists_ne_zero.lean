-- Prove2me | solution 1 for D1Bound5.finiteA4RowForm_exists_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:03:00.354982+00:00
-- url     : https://prove2.me/submissions/8861e258-6a15-49c5-9472-f94bfea75f6c

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
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_FiniteA4IntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions

section
namespace D1Bound5
variable {R : Type*} [CommRing R]

















set_option maxHeartbeats 12000000 in
/-- Exact determinant of the actual integral polynomial matrix. -/
theorem finiteA4DividedMatrix_det (x y c : R) :
    (finiteA4DividedMatrix x y c).det = 2910600*(x*y)^1*c^1*(x-y)^15 := by
  simp [finiteA4DividedMatrix,finiteA4Constant,finiteA4Left,finiteA4Right,
    Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.submatrix]
  <;> ring



theorem finiteA4DividedMatrix_det_ne_zero
    {F : Type*} [Field F] [CharZero F] (x y c : F)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y) :
    (finiteA4DividedMatrix x y c).det ≠ 0 := by
  rw [finiteA4DividedMatrix_det]
  norm_num [mul_eq_zero,sub_eq_zero,hx,hy,hc,hxy]

end D1Bound5
end

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]













theorem _root_.solution
    {F : Type*} [Field F] [CharZero F]
    (x y c z sX sY : F) (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y) (hz : z ≠ 0) :
    ∃ i : Fin 3, finiteA4RowForm x y c z sX sY i ≠ 0 := by
  classical
  let Q := finiteA4DividedMatrix x y c
  let v : Fin 3 → F := ![z,sX,sY]
  have hdet : Q.det ≠ 0 := finiteA4DividedMatrix_det_ne_zero x y c hx hy hc hxy
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
