-- Prove2me | solution 1 for D1Bound5.three_small_fixed_upper_and_overlap
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:37.303826+00:00
-- url     : https://prove2.me/submissions/4d157a7f-0a30-49a5-98af-16b38f68b7ee

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
namespace D1Bound5





theorem _root_.solution (C D : ℝ) (hC : (10 : ℝ)^40 ≤ C)
    (hD : D < (10 : ℝ)^60*C^7) :
    D < C^11/(10 : ℝ)^22 ∧ (10 : ℝ)^40*C^5 ≤ C^7/(10 : ℝ)^29 := by
  have hC0 : 0 < C := by norm_num at hC; linarith only [hC]
  have hC4 : (10 : ℝ)^160 ≤ C^4 := by
    have hh : ((10 : ℝ)^40)^4 ≤ C^4 := by gcongr
    norm_num at hh ⊢
    exact hh
  have hC2 : (10 : ℝ)^80 ≤ C^2 := by
    have hh : ((10 : ℝ)^40)^2 ≤ C^2 := by gcongr
    norm_num at hh ⊢
    exact hh
  constructor
  · apply lt_trans hD
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 10^22)).2
    have hh := mul_le_mul_of_nonneg_right hC4 (by positivity : 0 ≤ C^7)
    norm_num at hh ⊢
    nlinarith only [hh,pow_pos hC0 7]
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < 10^29)).2
    have hh := mul_le_mul_of_nonneg_right hC2 (by positivity : 0 ≤ C^5)
    norm_num at hh ⊢
    nlinarith only [hh,pow_nonneg hC0.le 5]





end D1Bound5
end
