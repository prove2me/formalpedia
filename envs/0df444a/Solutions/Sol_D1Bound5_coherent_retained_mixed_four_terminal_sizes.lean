-- Prove2me | solution 1 for D1Bound5.coherent_retained_mixed_four_terminal_sizes
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:42:35.36492+00:00
-- url     : https://prove2.me/submissions/488825ba-9bb7-4dbf-ad05-fbd22e7c0e3b

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



/-- The repeated retained power gap supplies the direct-four separation
and excludes the zero-form upper window. -/
theorem _root_.solution
    (A B S T C D : ℝ) (hA : 1 ≤ A) (hB : 3 ≤ B)
    (hS : 0 < S) (hT : 0 < T) (hST : S ≤ T) (hSC : S ≤ C)
    (hC1000 : 1000 < C) (hC : 16*B*S*T < C)
    (hD : A^2*C^5/S^2 < D) :
    1000*C < D ∧ 17*A*B*S*T*C^3 < D := by
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := by linarith only [hB]
  have hC0 : 0 < C := by linarith only [hC1000]
  have hA2 : (1 : ℝ) ≤ A^2 := by nlinarith only [hA,sq_nonneg (A-1)]
  constructor
  · have hC2 : (1000 : ℝ) < C^2 := by nlinarith only [hC1000,sq_nonneg (C-1000)]
    have hstart : 1000*C < C^3 := by
      have hh := mul_lt_mul_of_pos_right hC2 hC0
      nlinarith only [hh]
    have hfinish : C^3 ≤ A^2*C^5/S^2 := by
      apply (le_div_iff₀ (pow_pos hS 2)).2
      have hs : S^2 ≤ C^2 := by gcongr
      have hmul := mul_le_mul_of_nonneg_left hs (pow_nonneg hC0.le 3)
      have ha := mul_le_mul_of_nonneg_right hA2 (pow_nonneg hC0.le 5)
      nlinarith only [hmul,ha]
    exact (hstart.trans_le hfinish).trans hD
  · have hAB : 3 ≤ A*B := by
      nlinarith only [hA,hB,mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
    have hcoef : 17*A*B < 256*A^2*B^2 := by
      have hh := mul_pos (show 0 < A*B by positivity)
        (show 0 < 256*A*B-17 by linarith only [hAB])
      nlinarith only [hh]
    have hC2 : (16*B*S*T)^2 < C^2 := by gcongr
    have hC2' := mul_lt_mul_of_pos_left hC2 (pow_pos hA0 2)
    have hcoef' := mul_lt_mul_of_pos_right hcoef (by positivity : 0 < S^2*T^2)
    have hST' : 17*A*B*S^3*T ≤ 17*A*B*S^2*T^2 := by
      have hh := mul_le_mul_of_nonneg_left hST (by positivity : 0 ≤ 17*A*B*S^2*T)
      nlinarith only [hh]
    have hbase : 17*A*B*S*T < A^2*C^2/S^2 := by
      apply (lt_div_iff₀ (pow_pos hS 2)).2
      nlinarith only [hC2',hcoef',hST']
    have hh := mul_lt_mul_of_pos_right hbase (pow_pos hC0 3)
    have heq : (A^2*C^2/S^2)*C^3 = A^2*C^5/S^2 := by ring
    rw [heq] at hh
    exact hh.trans hD



end D1Bound5
end
