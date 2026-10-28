-- Prove2me | solution 1 for D1Bound5.finiteA5Residual_explicit
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:51.10375+00:00
-- url     : https://prove2.me/submissions/c08990e0-b793-4c12-95ad-e6bfbd7981e1

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
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_FiniteA5Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteA5Residual_Definitions
import Theorems.Thm_D1Bound5_bennettTwoNodes_branch_one_two
import Theorems.Thm_D1Bound5_bennettTwoNodes_zero

section
namespace D1Bound5
variable {R : Type*} [CommRing R]

























@[simp] theorem finiteA5Matrix_zero (x y c : R) (i : Fin 3) :
    finiteA5Matrix x y c i 0 = finiteA5Constant x y c i := by
  simp [finiteA5Matrix,finiteA5DividedMatrix,Matrix.mul_diagonal]
@[simp] theorem finiteA5Matrix_one (x y c : R) (i : Fin 3) :
    finiteA5Matrix x y c i 1 = x*finiteA5Left x y c i := by
  simp [finiteA5Matrix,finiteA5DividedMatrix,Matrix.mul_diagonal,mul_comm]
@[simp] theorem finiteA5Matrix_two (x y c : R) (i : Fin 3) :
    finiteA5Matrix x y c i 2 = y*finiteA5Right x y c i := by
  simp [finiteA5Matrix,finiteA5DividedMatrix,Matrix.mul_diagonal,mul_comm]







end D1Bound5
end
section
open scoped NumberField
open Module

namespace D1Bound5

theorem _root_.solution (x y c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (i : Fin 3) :
    finiteA5Residual x y c i = finiteA5Constant x y c i +
      x*finiteA5Left x y c i*(1+1/(x*c))^(1/2 : ℂ) +
      y*finiteA5Right x y c i*(1+1/(y*c))^(1/2 : ℂ) := by
  obtain ⟨h1,h2⟩ := bennettTwoNodes_branch_one_two x y c hx hy hc
  rw [finiteA5Residual,Fin.sum_univ_three,h1,h2]
  simp [bennettTwoNodes_zero]







end D1Bound5
end

