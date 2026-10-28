-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.two_small_fifth_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T22:53:09.356132+00:00
-- url     : https://prove2.me/submissions/4b445e7e-d001-434c-bf58-285b162cc36d

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
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_IsD1Tuple_two_small_bounded_fourth_fifth_lt
import Theorems.Thm_D1Bound5_IsD1Tuple_two_small_fourth_bound
import Theorems.Thm_D1Bound5_IsD1Tuple_two_small_large_third_bound

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5



/-- The complete analytic two-small cutoff for the fifth entry of an
actual ordered sextuple over the full integer ring. All finite families,
coherent forms, determinant growth and ordinary height bounds are
constructed internally; the only size assumptions specify the branch. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hB3 : ‖phi (a 1 : K)‖ < 3) (hS3 : 3 ≤ ‖phi (a 2 : K)‖) :
    ‖phi (a 4 : K)‖ < (10 : ℝ)^550 := by
  have hCD : ‖phi (a 4 : K)‖ ≤ ‖phi (a 5 : K)‖ := hmon (by decide)
  by_cases hS : (10 : ℝ)^8 ≤ ‖phi (a 2 : K)‖
  · have hh := (ha.two_small_large_third_bound hK phi a hmon hB3 hS).2
    exact (hCD.trans_lt hh).trans (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 10) (by decide : 396 < 550))
  · have hSsmall : ‖phi (a 2 : K)‖ < (10 : ℝ)^8 := lt_of_not_ge hS
    by_cases hT : (10 : ℝ)^8 ≤ ‖phi (a 3 : K)‖
    · have hh := (ha.two_small_fourth_bound hK phi a hmon hB3 hS3 hSsmall).2 hT
      exact (hCD.trans_lt hh).trans (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 10) (by decide : 549 < 550))
    · have hh := ha.two_small_bounded_fourth_fifth_lt hK phi a hmon hB3 hS3 (lt_of_not_ge hT)
      exact hh.trans (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 10) (by decide : 100 < 550))

end D1Bound5
end
