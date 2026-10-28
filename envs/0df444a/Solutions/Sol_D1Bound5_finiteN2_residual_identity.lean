-- Prove2me | solution 1 for D1Bound5.finiteN2_residual_identity
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:27:43.233047+00:00
-- url     : https://prove2.me/submissions/be2a9264-fd23-4a9a-8578-4e044fa69084

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
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteN2Residual_Definitions
import Theorems.Thm_D1Bound5_bennettTwoNodes_branch_one_two
import Theorems.Thm_D1Bound5_bennettTwoNodes_zero
import Theorems.Thm_D1Bound5_finiteN2_bennett_identity

section
namespace D1Bound5

variable {R : Type*} [CommRing R]













@[simp] theorem finiteN2Matrix_zero (x y c : R) (i : Fin 3) :
    finiteN2Matrix x y c i 0 = finiteN2Constant x y c i := by
  simp [finiteN2Matrix, finiteN2DividedMatrix, Matrix.mul_diagonal]

@[simp] theorem finiteN2Matrix_one (x y c : R) (i : Fin 3) :
    finiteN2Matrix x y c i 1 = x * finiteN2Left x y c i := by
  simp [finiteN2Matrix, finiteN2DividedMatrix, Matrix.mul_diagonal, mul_comm]

@[simp] theorem finiteN2Matrix_two (x y c : R) (i : Fin 3) :
    finiteN2Matrix x y c i 2 = y * finiteN2Right x y c i := by
  simp [finiteN2Matrix, finiteN2DividedMatrix, Matrix.mul_diagonal, mul_comm]







end D1Bound5
end

section
namespace D1Bound5



theorem _root_.solution (x y c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y) (i : Fin 3) :
    (∑ j, bennettTwoClearedEntry x y c 2 i j *
      (1+bennettTwoNodes x y j*(x*y*c)⁻¹)^(1/2 : ℂ)) =
      2*finiteN2RowFactor x y i*finiteN2Residual x y c i := by
  obtain ⟨hX,hY⟩ := bennettTwoNodes_branch_one_two x y c hx hy hc
  simp_rw [finiteN2_bennett_identity x y c hx hy hxy]
  rw [Fin.sum_univ_three, finiteN2Matrix_zero, finiteN2Matrix_one,
    finiteN2Matrix_two, hX, hY]
  simp [bennettTwoNodes_zero, finiteN2Residual]
  <;> ring











end D1Bound5
end
