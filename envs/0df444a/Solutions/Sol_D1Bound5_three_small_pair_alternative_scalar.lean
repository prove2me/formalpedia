-- Prove2me | solution 1 for D1Bound5.three_small_pair_alternative_scalar
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:26:11.152834+00:00
-- url     : https://prove2.me/submissions/d417a249-ee64-4e3e-8de1-e31b129c4c2c

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

section
open scoped NumberField
open Module

namespace D1Bound5

theorem _root_.solution
    (A B S P Q : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) (hBS : B ≤ S) (hS : S < 3)
    (hP : 1000 ≤ P) (hPQ : P ≤ Q)
    (halt : (5*A*B*S*P^2 < Q ∧ Q < 15*A*B*S*P^2) ∨
      Q < 101*B^2*S^4/P ∨ A^2*P^5/(37*S^2) < Q) :
    (5*P^2 < Q ∧ Q < 405*P^2) ∨ P^5/400 < Q := by
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := hA0.trans_le hAB
  have hS0 : 0 < S := hB0.trans_le hBS
  have hB : 1 ≤ B := hA.trans hAB
  have hS1 : 1 ≤ S := hB.trans hBS
  have hA3 : A < 3 := (hAB.trans hBS).trans_lt hS
  have hB3 : B < 3 := hBS.trans_lt hS
  have hP0 : 0 < P := by linarith only [hP]
  rcases halt with hzero | hlow | hhigh
  · left
    have hAB1 : 1 ≤ A*B := by
      have hh := mul_le_mul hA hB (by norm_num : (0 : ℝ) ≤ 1) hA0.le
      simpa only [one_mul] using hh
    have hV : 1 ≤ A*B*S := by
      have hh := mul_le_mul hAB1 hS1 (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ A*B)
      simpa only [one_mul] using hh
    have hV27 : A*B*S < 27 := by
      calc
        _ < (3 : ℝ)*3*3 := by gcongr
        _ = _ := by norm_num
    have hlo := mul_le_mul_of_nonneg_right hV (sq_nonneg P)
    have hhi := mul_lt_mul_of_pos_right hV27 (sq_pos_of_pos hP0)
    constructor <;> nlinarith only [hzero.1,hzero.2,hlo,hhi]
  · have hcoeff : B^2*S^4 < (3 : ℝ)^2*3^4 := by gcongr
    have hh := (lt_div_iff₀ hP0).1 hlow
    have hPQ' := mul_le_mul_of_nonneg_right hPQ hP0.le
    have hP2 : (1000 : ℝ)^2 ≤ P^2 := by gcongr
    norm_num at hcoeff hP2
    exact False.elim (by nlinarith only [hcoeff,hh,hPQ',hP2])
  · right
    have hA2 : 1 ≤ A^2 := by nlinarith only [hA,sq_nonneg (A-1)]
    have hS2 : S^2 < (3 : ℝ)^2 := by gcongr
    have hcompare : P^5/400 < A^2*P^5/(37*S^2) := by
      apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 400) (by positivity)).2
      have hh := mul_lt_mul_of_pos_right hS2 (pow_pos hP0 5)
      have hh' := mul_le_mul_of_nonneg_right hA2 (by positivity : 0 ≤ P^5)
      nlinarith only [hh,hh',pow_pos hP0 5]
    exact hcompare.trans hhigh





end D1Bound5
end
