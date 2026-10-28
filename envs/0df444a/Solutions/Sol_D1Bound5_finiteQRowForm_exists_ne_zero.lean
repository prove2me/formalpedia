-- Prove2me | solution 1 for D1Bound5.finiteQRowForm_exists_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:26:15.716752+00:00
-- url     : https://prove2.me/submissions/fadbacf6-6587-4c5e-94a0-5562ffa3c3c4

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
import Definitions.Def_D1Bound5_FiniteQIntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteQMatrix_Definitions

section
namespace D1Bound5

variable {R : Type*} [CommRing R]

set_option maxRecDepth 4096 in
/-- Sparse determinant expansion before substituting the polynomial row entries. -/
private theorem finiteQSparseMatrix_det
    (c0 l0 r0 c1 l1 r1 c2 l2 r2 c3 l3 r3 c4 l4 r4 : R) :
    (!![c0,l0,r0,0,0; c1,l1,0,r1,0; c2,0,l2,r2,0;
        c3,l3,0,0,r3; c4,0,l4,0,r4] : Matrix (Fin 5) (Fin 5) R).det =
      (r4*c3-r3*c4)*(l0*r1*l2+r0*l1*r2) +
      r3*l4*(c0*l1*r2-l0*c1*r2+l0*r1*c2) -
      r4*l3*(c0*r1*l2+r0*c1*r2-r0*r1*c2) := by
  have hs1_0_0 : Fin.succAbove (0 : Fin 2) (0 : Fin 1) = (1 : Fin 2) := by decide
  have hs1_1_0 : Fin.succAbove (1 : Fin 2) (0 : Fin 1) = (0 : Fin 2) := by decide
  have hs2_0_0 : Fin.succAbove (0 : Fin 3) (0 : Fin 2) = (1 : Fin 3) := by decide
  have hs2_0_1 : Fin.succAbove (0 : Fin 3) (1 : Fin 2) = (2 : Fin 3) := by decide
  have hs2_1_0 : Fin.succAbove (1 : Fin 3) (0 : Fin 2) = (0 : Fin 3) := by decide
  have hs2_1_1 : Fin.succAbove (1 : Fin 3) (1 : Fin 2) = (2 : Fin 3) := by decide
  have hs2_2_0 : Fin.succAbove (2 : Fin 3) (0 : Fin 2) = (0 : Fin 3) := by decide
  have hs2_2_1 : Fin.succAbove (2 : Fin 3) (1 : Fin 2) = (1 : Fin 3) := by decide
  have hs3_0_0 : Fin.succAbove (0 : Fin 4) (0 : Fin 3) = (1 : Fin 4) := by decide
  have hs3_0_1 : Fin.succAbove (0 : Fin 4) (1 : Fin 3) = (2 : Fin 4) := by decide
  have hs3_0_2 : Fin.succAbove (0 : Fin 4) (2 : Fin 3) = (3 : Fin 4) := by decide
  have hs3_1_0 : Fin.succAbove (1 : Fin 4) (0 : Fin 3) = (0 : Fin 4) := by decide
  have hs3_1_1 : Fin.succAbove (1 : Fin 4) (1 : Fin 3) = (2 : Fin 4) := by decide
  have hs3_1_2 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = (3 : Fin 4) := by decide
  have hs3_2_0 : Fin.succAbove (2 : Fin 4) (0 : Fin 3) = (0 : Fin 4) := by decide
  have hs3_2_1 : Fin.succAbove (2 : Fin 4) (1 : Fin 3) = (1 : Fin 4) := by decide
  have hs3_2_2 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = (3 : Fin 4) := by decide
  have hs3_3_0 : Fin.succAbove (3 : Fin 4) (0 : Fin 3) = (0 : Fin 4) := by decide
  have hs3_3_1 : Fin.succAbove (3 : Fin 4) (1 : Fin 3) = (1 : Fin 4) := by decide
  have hs3_3_2 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = (2 : Fin 4) := by decide
  have hs4_0_0 : Fin.succAbove (0 : Fin 5) (0 : Fin 4) = (1 : Fin 5) := by decide
  have hs4_0_1 : Fin.succAbove (0 : Fin 5) (1 : Fin 4) = (2 : Fin 5) := by decide
  have hs4_0_2 : Fin.succAbove (0 : Fin 5) (2 : Fin 4) = (3 : Fin 5) := by decide
  have hs4_0_3 : Fin.succAbove (0 : Fin 5) (3 : Fin 4) = (4 : Fin 5) := by decide
  have hs4_1_0 : Fin.succAbove (1 : Fin 5) (0 : Fin 4) = (0 : Fin 5) := by decide
  have hs4_1_1 : Fin.succAbove (1 : Fin 5) (1 : Fin 4) = (2 : Fin 5) := by decide
  have hs4_1_2 : Fin.succAbove (1 : Fin 5) (2 : Fin 4) = (3 : Fin 5) := by decide
  have hs4_1_3 : Fin.succAbove (1 : Fin 5) (3 : Fin 4) = (4 : Fin 5) := by decide
  have hs4_2_0 : Fin.succAbove (2 : Fin 5) (0 : Fin 4) = (0 : Fin 5) := by decide
  have hs4_2_1 : Fin.succAbove (2 : Fin 5) (1 : Fin 4) = (1 : Fin 5) := by decide
  have hs4_2_2 : Fin.succAbove (2 : Fin 5) (2 : Fin 4) = (3 : Fin 5) := by decide
  have hs4_2_3 : Fin.succAbove (2 : Fin 5) (3 : Fin 4) = (4 : Fin 5) := by decide
  have hs4_3_0 : Fin.succAbove (3 : Fin 5) (0 : Fin 4) = (0 : Fin 5) := by decide
  have hs4_3_1 : Fin.succAbove (3 : Fin 5) (1 : Fin 4) = (1 : Fin 5) := by decide
  have hs4_3_2 : Fin.succAbove (3 : Fin 5) (2 : Fin 4) = (2 : Fin 5) := by decide
  have hs4_3_3 : Fin.succAbove (3 : Fin 5) (3 : Fin 4) = (4 : Fin 5) := by decide
  have hs4_4_0 : Fin.succAbove (4 : Fin 5) (0 : Fin 4) = (0 : Fin 5) := by decide
  have hs4_4_1 : Fin.succAbove (4 : Fin 5) (1 : Fin 4) = (1 : Fin 5) := by decide
  have hs4_4_2 : Fin.succAbove (4 : Fin 5) (2 : Fin 4) = (2 : Fin 5) := by decide
  have hs4_4_3 : Fin.succAbove (4 : Fin 5) (3 : Fin 4) = (3 : Fin 5) := by decide
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix,
    hs1_0_0, hs1_1_0, hs2_0_0, hs2_0_1, hs2_1_0, hs2_1_1, hs2_2_0, hs2_2_1, hs3_0_0, hs3_0_1, hs3_0_2, hs3_1_0, hs3_1_1, hs3_1_2, hs3_2_0, hs3_2_1, hs3_2_2, hs3_3_0, hs3_3_1, hs3_3_2, hs4_0_0, hs4_0_1, hs4_0_2, hs4_0_3, hs4_1_0, hs4_1_1, hs4_1_2, hs4_1_3, hs4_2_0, hs4_2_1, hs4_2_2, hs4_2_3, hs4_3_0, hs4_3_1, hs4_3_2, hs4_3_3, hs4_4_0, hs4_4_1, hs4_4_2, hs4_4_3]
  <;> ring











set_option maxHeartbeats 2000000 in
/-- Exact determinant of the divided finite family. In particular all
dependence on c cancels; this is checked by polynomial identities. -/
theorem finiteQDividedMatrix_det (a b s t c : R) :
    (finiteQDividedMatrix a b s t c).det =
      180*a*b*s*t*(a-b)^2*(a-s)*(a-t)*(b-s)*(b-t)*(s-t) := by
  rw [finiteQDividedMatrix, finiteQSparseMatrix_det]
  unfold finiteQConstant finiteQLeft finiteQRight
  ring



theorem finiteQDividedMatrix_det_ne_zero
    {F : Type*} [Field F] [CharZero F] (a b s t c : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hat : a ≠ t)
    (hbs : b ≠ s) (hbt : b ≠ t) (hst : s ≠ t) :
    (finiteQDividedMatrix a b s t c).det ≠ 0 := by
  rw [finiteQDividedMatrix_det]
  norm_num [mul_eq_zero, sub_eq_zero, ha, hb, hs, ht, hab, has, hat, hbs, hbt, hst]

end D1Bound5
end

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]













/-- The actual finite determinant selects a nonzero row from a nonzero
terminal root, independently of the choice of signed product roots. -/
theorem _root_.solution
    {F : Type*} [Field F] [CharZero F]
    (a b s t c z rA rB rS rT : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hat : a ≠ t)
    (hbs : b ≠ s) (hbt : b ≠ t) (hst : s ≠ t) (hz : z ≠ 0) :
    ∃ i : Fin 5, finiteQRowForm a b s t c z rA rB rS rT i ≠ 0 := by
  classical
  let Q := finiteQDividedMatrix a b s t c
  let v : Fin 5 → F := ![z, rA, rB, rS, rT]
  have hdet : Q.det ≠ 0 := finiteQDividedMatrix_det_ne_zero a b s t c
    ha hb hs ht hab has hat hbs hbt hst
  have hunit : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).2
    (isUnit_iff_ne_zero.mpr hdet)
  have hinj : Function.Injective Q.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hunit
  by_contra h
  push_neg at h
  have hzero : Q.mulVec v = 0 := by
    funext i
    exact h i
  have hv : v = 0 := hinj (by simpa using hzero)
  exact hz (by simpa [v] using congrFun hv (0 : Fin 5))



end D1Bound5
end
