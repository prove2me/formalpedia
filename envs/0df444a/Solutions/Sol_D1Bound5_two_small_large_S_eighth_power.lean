-- Prove2me | solution 1 for D1Bound5.two_small_large_S_eighth_power
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:42.287503+00:00
-- url     : https://prove2.me/submissions/ba1bbeb8-5aa1-4c20-a637-560987786eef

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



/-- Once the V window is exited on its upper side, the eighth-power
growth follows by elementary positive-power comparisons. -/
theorem _root_.solution
    (A S T C D : ℝ) (hA : 1 ≤ A) (hS : 0 < S) (hST : S ≤ T)
    (hC : (3/8 : ℝ)*A*S*T < C)
    (hV : (2/5 : ℝ)*A^2*C^5/T^2 < D) :
    S^8/(10 : ℝ)^4 < D := by
  have hA0 : 0 < A := by linarith only [hA]
  have hT : 0 < T := hS.trans_le hST
  have hC4 : S*T/4 < C := by
    have hh := mul_le_mul_of_nonneg_right hA (mul_nonneg hS.le hT.le)
    nlinarith only [hC,hh,mul_pos hS hT]
  have hC0 : 0 < C := (by positivity : 0 < S*T/4).trans hC4
  have hC5 : (S*T/4)^5 < C^5 := by gcongr
  have hA2 : (1 : ℝ) ≤ A^2 := by nlinarith only [hA,sq_nonneg (A-1)]
  have hmain : S^5*T^3/2560 < (2/5 : ℝ)*A^2*C^5/T^2 := by
    have hscaled := mul_lt_mul_of_pos_left hC5 (by norm_num : (0 : ℝ) < 2/5)
    have hscaled' := mul_le_mul_of_nonneg_right hA2 (by positivity : 0 ≤ (2/5 : ℝ)*C^5)
    apply (lt_div_iff₀ (sq_pos_of_pos hT)).2
    nlinarith only [hscaled,hscaled']
  have hST3 : S^3 ≤ T^3 := by gcongr
  have hS8 : S^8 ≤ S^5*T^3 := by
    have hh := mul_le_mul_of_nonneg_left hST3 (by positivity : 0 ≤ S^5)
    nlinarith only [hh]
  have hsmall : S^8/(10 : ℝ)^4 < S^5*T^3/2560 := by
    norm_num
    nlinarith only [hS8,pow_pos hS 8]
  exact hsmall.trans (hmain.trans hV)

end D1Bound5
end
