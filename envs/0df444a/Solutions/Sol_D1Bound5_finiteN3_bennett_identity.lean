-- Prove2me | solution 1 for D1Bound5.finiteN3_bennett_identity
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:15.933046+00:00
-- url     : https://prove2.me/submissions/2d4c5a11-ff53-4fb6-b6bc-8e5026b5803e

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_FiniteN3Matrix_Definitions
import Theorems.Thm_D1Bound5_bennettClearedTaylor_two_poles_scaled_eval
import Theorems.Thm_D1Bound5_bennettTwoNodes_one
import Theorems.Thm_D1Bound5_bennettTwoNodes_two
import Theorems.Thm_D1Bound5_bennettTwoNodes_zero
import Theorems.Thm_D1Bound5_bennettTwoOtherPoles_one
import Theorems.Thm_D1Bound5_bennettTwoOtherPoles_two
import Theorems.Thm_D1Bound5_bennettTwoOtherPoles_zero
import Theorems.Thm_D1Bound5_finiteN3_choose_three
import Theorems.Thm_D1Bound5_finiteN3_choose_two

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]





set_option maxHeartbeats 4000000 in
/-- Exact identification of the N3 integer polynomials with the actual
ordinary Bennett matrix at k=3. The row factors are precisely
4(x-y),4x,4y; no residue identity is supplied as a hypothesis. -/
theorem _root_.solution (x y c : F)
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) (i j : Fin 3) :
    bennettTwoClearedEntry x y c 3 i j =
      4 * finiteN3RowFactor x y i * finiteN3Matrix x y c i j := by
  have hfin01 : (0 : Fin 3) ≠ 1 := by decide
  have hfin02 : (0 : Fin 3) ≠ 2 := by decide
  have hfin10 : (1 : Fin 3) ≠ 0 := by decide
  have hfin12 : (1 : Fin 3) ≠ 2 := by decide
  have hfin20 : (2 : Fin 3) ≠ 0 := by decide
  have hfin21 : (2 : Fin 3) ≠ 1 := by decide
  have hanti0 : Finset.antidiagonal 0 = {(0,0)} := by decide
  have hanti1 : Finset.antidiagonal 1 = {(0,1),(1,0)} := by decide
  have hanti2 : Finset.antidiagonal 2 = {(0,2),(1,1),(2,0)} := by decide
  have hanti3 : Finset.antidiagonal 3 = {(0,3),(1,2),(2,1),(3,0)} := by decide
  have hd : x-y ≠ 0 := sub_ne_zero.mpr hxy
  have hd' : y-x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
  all_goals
    unfold bennettTwoClearedEntry bennettClearedResidue
    first
    | rw [bennettTwoOtherPoles_zero, bennettTwoNodes_zero,
        bennettClearedTaylor_two_poles_scaled_eval]
    | rw [bennettTwoOtherPoles_one, bennettTwoNodes_one,
        bennettClearedTaylor_two_poles_scaled_eval]
    | rw [bennettTwoOtherPoles_two, bennettTwoNodes_two,
        bennettClearedTaylor_two_poles_scaled_eval]
    norm_num [hfin01, hfin02, hfin10, hfin12, hfin20, hfin21, hanti1, hanti2, hanti3, hanti0,
      Ring.choose_zero_right, Ring.choose_one_right, finiteN3_choose_two, finiteN3_choose_three,
      finiteN3RowFactor, finiteN3Matrix, finiteN3DividedMatrix,
      Matrix.mul_diagonal, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, finiteN3Constant, finiteN3Left, finiteN3Right]
    field_simp [hx, hy, hd, hd']
    <;> ring

end D1Bound5
end
