-- Prove2me | solution 1 for D1Bound5.coherent_retained_mixed_first_terminal_large
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:35.070443+00:00
-- url     : https://prove2.me/submissions/1cfbc062-c57f-4ee1-b6bb-366b339b422f

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
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
    (A B S T C : ℝ) (hA : 1 ≤ A) (hB : 3 ≤ B) (hS : 0 < S)
    (hBS : B ≤ S) (hST : S ≤ T)
    (hfront : 2*A*B*S < T) (hgap : A^2*T^5/S^2 < C) :
    16*B*S*T < C := by
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := by linarith only [hB]
  have hT : 0 < T := hS.trans_le hST
  have hBT : B ≤ T := hBS.trans hST
  have hAB : 3 ≤ A*B := by
    nlinarith only [hA,hB,mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
  have h2S : 6*S < T := by
    have hh := mul_le_mul_of_nonneg_right hAB hS.le
    nlinarith only [hh,hfront,hS]
  have hT2 : 36*S^2 ≤ T^2 := by
    have hh := mul_pos (sub_pos.mpr h2S) (show 0 < T+6*S by positivity)
    nlinarith only [hh]
  have hsmall : 16*B*S*T ≤ 16*T^3 := by
    calc
      16*B*S*T ≤ 16*T*T*T := by gcongr
      _ = _ := by ring
  have hA2 : (1 : ℝ) ≤ A^2 := by nlinarith only [hA,sq_nonneg (A-1)]
  have hmiddle : 16*T^3 < 36*A^2*T^3 := by
    have hh := mul_pos (show 0 < 36*A^2-16 by linarith only [hA2]) (pow_pos hT 3)
    nlinarith only [hh]
  have hlarge : 36*A^2*T^3 ≤ A^2*T^5/S^2 := by
    apply (le_div_iff₀ (pow_pos hS 2)).2
    have hh := mul_le_mul_of_nonneg_left hT2 (by positivity : 0 ≤ A^2*T^3)
    nlinarith only [hh]
  exact (hsmall.trans_lt (hmiddle.trans_le hlarge)).trans hgap





end D1Bound5
end
