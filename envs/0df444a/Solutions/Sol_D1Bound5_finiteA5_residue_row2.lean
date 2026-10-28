-- Prove2me | solution 1 for D1Bound5.finiteA5_residue_row2
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:37:57.312996+00:00
-- url     : https://prove2.me/submissions/1e825b71-b897-4cbc-abe7-2be36d155de0

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_FiniteA5Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteUnequalEntry_Definitions
import Theorems.Thm_D1Bound5_bennettClearedTaylor_two_poles_scaled_eval
import Theorems.Thm_D1Bound5_bennettTwoNodes_one
import Theorems.Thm_D1Bound5_bennettTwoNodes_two
import Theorems.Thm_D1Bound5_bennettTwoNodes_zero
import Theorems.Thm_D1Bound5_finiteA_choose_five
import Theorems.Thm_D1Bound5_finiteA_choose_four
import Theorems.Thm_D1Bound5_finiteA_choose_three
import Theorems.Thm_D1Bound5_finiteA_choose_two
import Theorems.Thm_D1Bound5_finiteUnequalOtherPoles_one
import Theorems.Thm_D1Bound5_finiteUnequalOtherPoles_two
import Theorems.Thm_D1Bound5_finiteUnequalOtherPoles_zero

section
namespace D1Bound5
variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 12000000 in
/-- One complete matrix row of the original A5 residue identity.
All three columns remain quantified and are covered by exact finite cases. -/
theorem _root_.solution (x y c : F)
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) (j : Fin 3) :
    finiteUnequalClearedEntry x y c 5 4 2 j =
      4*finiteA5RowFactor x y 2*finiteA5Matrix x y c 2 j := by
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
  have hanti4 : Finset.antidiagonal 4 = {(0,4),(1,3),(2,2),(3,1),(4,0)} := by decide
  have hanti5 : Finset.antidiagonal 5 = {(0,5),(1,4),(2,3),(3,2),(4,1),(5,0)} := by decide
  have hd : x-y ≠ 0 := sub_ne_zero.mpr hxy
  have hd' : y-x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  all_goals
    unfold finiteUnequalClearedEntry
    first
    | rw [finiteUnequalOtherPoles_zero x y 5 4 (by decide) (by decide),
        bennettTwoNodes_zero, bennettClearedTaylor_two_poles_scaled_eval]
    | rw [finiteUnequalOtherPoles_one x y 5 4 (by decide) (by decide),
        bennettTwoNodes_one, bennettClearedTaylor_two_poles_scaled_eval]
    | rw [finiteUnequalOtherPoles_two x y 5 4 (by decide) (by decide),
        bennettTwoNodes_two, bennettClearedTaylor_two_poles_scaled_eval]
    norm_num [hfin01,hfin02,hfin10,hfin12,hfin20,hfin21,hanti0,hanti1,hanti2,hanti3,hanti4,hanti5,
      finiteUnequalOrders,Ring.choose_zero_right,Ring.choose_one_right,
      finiteA_choose_two,finiteA_choose_three,finiteA_choose_four,finiteA_choose_five,
      finiteA5RowFactor,finiteA5Matrix,finiteA5DividedMatrix,Matrix.mul_diagonal,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      finiteA5Constant,finiteA5Left,finiteA5Right]
    field_simp [hx,hy,hd,hd']
    <;> ring

end D1Bound5
end
