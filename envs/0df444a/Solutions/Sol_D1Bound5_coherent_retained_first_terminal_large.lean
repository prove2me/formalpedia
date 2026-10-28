-- Prove2me | solution 1 for D1Bound5.coherent_retained_first_terminal_large
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:15:56.671985+00:00
-- url     : https://prove2.me/submissions/4be28986-31a4-4f9d-b9d0-48e1e0d04268

import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- The first retained power gap separates the fourth anchor from the
first terminal by the factor needed in the direct-four estimate. -/
theorem _root_.solution
    (A B S T C : ℝ) (hA : 3 ≤ A) (hB : 3 ≤ B) (hS : 0 < S)
    (hBS : B ≤ S) (hST : S ≤ T)
    (hfront : 2*A*B*S < T) (hgap : A^2*T^5/S^2 < C) :
    16*B*S*T < C := by
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := by linarith only [hB]
  have hT : 0 < T := hS.trans_le hST
  have hBT : B ≤ T := hBS.trans hST
  have hAB : 9 ≤ A*B := by
    nlinarith only [hA,hB,mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
  have h2S : 2*S < T := by
    have hh := mul_le_mul_of_nonneg_right hAB hS.le
    nlinarith only [hh,hfront,hS]
  have hT2 : 4*S^2 ≤ T^2 := by
    have hh := mul_pos (sub_pos.mpr h2S) (show 0 < T+2*S by positivity)
    nlinarith only [hh]
  have hsmall : 16*B*S*T ≤ 16*T^3 := by
    calc
      16*B*S*T ≤ 16*T*T*T := by gcongr
      _ = _ := by ring
  have hA2 : (9 : ℝ) ≤ A^2 := by nlinarith only [hA,sq_nonneg (A-3)]
  have hmiddle : 16*T^3 < 4*A^2*T^3 := by
    have hh := mul_pos (show 0 < 4*A^2-16 by linarith only [hA2]) (pow_pos hT 3)
    nlinarith only [hh]
  have hlarge : 4*A^2*T^3 ≤ A^2*T^5/S^2 := by
    apply (le_div_iff₀ (pow_pos hS 2)).2
    have hh := mul_le_mul_of_nonneg_left hT2 (by positivity : 0 ≤ A^2*T^3)
    nlinarith only [hh]
  exact (hsmall.trans_lt (hmiddle.trans_le hlarge)).trans hgap



end D1Bound5
end
