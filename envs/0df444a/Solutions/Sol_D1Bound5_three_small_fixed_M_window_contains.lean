-- Prove2me | solution 1 for D1Bound5.three_small_fixed_M_window_contains
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:37:54.856542+00:00
-- url     : https://prove2.me/submissions/73700912-29bb-4379-8e2c-bd1f8da00e8b

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







theorem _root_.solution
    (A B S C : ℝ) (hA : 1 ≤ A) (hB : 0 < B) (hB3 : B < 3)
    (hS : 0 < S) (hS3 : S < 3) (hC : 0 < C) :
    4*((8/9 : ℝ)*608^2)^2*B^6*S^16*C^5/(1-1/4000 : ℝ) ≤ (10 : ℝ)^40*C^5 ∧
      C^11/(10 : ℝ)^22 ≤ A^6*C^11/(4*(3920/81 : ℝ)^2*B^4*S^10*(1+1/4000 : ℝ)) := by
  constructor
  · have hp : B^6*S^16 < (3 : ℝ)^22 := by
      calc
        _ < (3 : ℝ)^6*3^16 := by gcongr
        _ = _ := by norm_num
    have hh := mul_lt_mul_of_pos_right hp (by positivity : 0 < C^5)
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1-1/4000)).2
    norm_num at hh ⊢
    nlinarith only [hh,pow_nonneg hC.le 5]
  · have hp : B^4*S^10 < (3 : ℝ)^14 := by
      calc
        _ < (3 : ℝ)^4*3^10 := by gcongr
        _ = _ := by norm_num
    have hd : 4*(3920/81 : ℝ)^2*B^4*S^10*(1+1/4000 : ℝ) ≤ (10 : ℝ)^22 := by
      norm_num at hp ⊢
      nlinarith only [hp]
    have hA6 : 1 ≤ A^6 := by calc
      1 = (1 : ℝ)^6 := by norm_num
      _ ≤ A^6 := by gcongr
    calc
      _ ≤ C^11/(4*(3920/81 : ℝ)^2*B^4*S^10*(1+1/4000 : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hd
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hh := mul_le_mul_of_nonneg_right hA6 (by positivity : 0 ≤ C^11)
        simpa only [one_mul] using hh



end D1Bound5
end
