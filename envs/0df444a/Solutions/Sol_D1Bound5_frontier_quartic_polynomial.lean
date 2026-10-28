-- Prove2me | solution 1 for D1Bound5.frontier_quartic_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:52:08.788316+00:00
-- url     : https://prove2.me/submissions/1845533c-291f-4cc9-bab6-11d5c545cda6

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg

section
namespace D1Bound5





/-- The quartic determinant polynomial has nine absolute coefficient
units when its three disjoint-edge products have modulus at most L. -/
theorem _root_.solution (P Q R : ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hP : ‖P‖ ≤ L) (hQ : ‖Q‖ ≤ L) (hR : ‖R‖ ≤ L) :
    ‖P^2+Q^2+R^2-2*(P*Q+P*R+Q*R)‖ ≤ 9*L^2 := by
  have hpair (x y : ℂ) (hx : ‖x‖ ≤ L) (hy : ‖y‖ ≤ L) : ‖x*y‖ ≤ L^2 := by
    rw [norm_mul]
    nlinarith only [mul_le_mul hx hy (norm_nonneg _) hL]
  have hPP := hpair P P hP hP
  have hQQ := hpair Q Q hQ hQ
  have hRR := hpair R R hR hR
  have hPQ := hpair P Q hP hQ
  have hPR := hpair P R hP hR
  have hQR := hpair Q R hQ hR
  have hs1 : ‖P^2+Q^2+R^2‖ ≤ 3*L^2 := by
    have h1 := norm_add_le (P^2+Q^2) (R^2)
    have h2 := norm_add_le (P^2) (Q^2)
    simp only [← pow_two] at hPP hQQ hRR
    linarith only [h1, h2, hPP, hQQ, hRR]
  have hs2 : ‖P*Q+P*R+Q*R‖ ≤ 3*L^2 := by
    have h1 := norm_add_le (P*Q+P*R) (Q*R)
    have h2 := norm_add_le (P*Q) (P*R)
    linarith only [h1, h2, hPQ, hPR, hQR]
  have h := norm_sub_le (P^2+Q^2+R^2) (2*(P*Q+P*R+Q*R))
  rw [norm_mul, Complex.norm_two] at h
  linarith only [h, hs1, hs2]

end D1Bound5
end
