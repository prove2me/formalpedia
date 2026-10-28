-- Prove2me | solution 1 for D1Bound5.three_small_three_large_impossible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T22:58:29.836222+00:00
-- url     : https://prove2.me/submissions/f66a47d0-8f72-422d-8e54-04508c9bcdc3

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
import Theorems.Thm_D1Bound5_three_small_pair_growth
import Theorems.Thm_D1Bound5_three_small_tenth_growth_impossible

section
open scoped NumberField
open Module

namespace D1Bound5





theorem _root_.solution
    (U V W : ℝ) (hU : (10 : ℝ)^40 ≤ U)
    (hUV : (5*U^2 < V ∧ V < 405*U^2) ∨ U^5/400 < V)
    (hVW : (5*V^2 < W ∧ W < 405*V^2) ∨ V^5/400 < W)
    (hUW : (5*U^2 < W ∧ W < 405*U^2) ∨ U^5/400 < W)
    (hupper : W < (10 : ℝ)^60*U^7) : False := by
  have hU0 : 0 < U := by norm_num at hU; linarith only [hU]
  have hU1000 : 1000 ≤ U := by norm_num at hU; linarith only [hU]
  have hVgrow := three_small_pair_growth U V hU1000 hUV
  have hV0 : 0 < V := (by positivity : 0 < 5*U^2).trans hVgrow
  have hV1000 : 1000 ≤ V := by nlinarith only [hVgrow,hU1000,sq_nonneg (U-1000)]
  have hWgrow := three_small_pair_growth V W hV1000 hVW
  rcases hUV with hUV | hUV
  · rcases hVW with hVW | hVW
    · have hv2hi : V^2 < (405*U^2)^2 := by
        gcongr
        exact hUV.2
      have hv2lo : (5*U^2)^2 < V^2 := by gcongr
      have hWlo : 125*U^4 < W := by nlinarith only [hVW.1,hv2lo]
      have hWhi : W < 405^3*U^4 := by nlinarith only [hVW.2,hv2hi]
      rcases hUW with hUW | hUW
      · have hU2 : (1000 : ℝ)^2 ≤ U^2 := by gcongr
        have hh := mul_le_mul_of_nonneg_right hU2 (sq_nonneg U)
        norm_num at hh
        nlinarith only [hWlo,hUW.2,hh,sq_pos_of_pos hU0]
      · have hh := mul_le_mul_of_nonneg_right hU (by positivity : 0 ≤ U^4)
        norm_num at hh
        nlinarith only [hWhi,hUW,hh,pow_pos hU0 4]
    · have hv5 : (5*U^2)^5 < V^5 := by gcongr
      have hlow : U^10/32000 < W := by
        nlinarith only [hv5,hVW,pow_pos hU0 10]
      exact three_small_tenth_growth_impossible U W hU hlow hupper
  · have hv2 : (U^5/400)^2 < V^2 := by gcongr
    have hlow : U^10/32000 < W := by nlinarith only [hv2,hWgrow]
    exact three_small_tenth_growth_impossible U W hU hlow hupper





end D1Bound5
end
