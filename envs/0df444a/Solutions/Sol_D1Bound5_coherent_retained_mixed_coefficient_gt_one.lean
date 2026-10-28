-- Prove2me | solution 1 for D1Bound5.coherent_retained_mixed_coefficient_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:02.330432+00:00
-- url     : https://prove2.me/submissions/6adbb6ab-3b35-4672-8551-48e8aa94f84c

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
open Finset
open scoped NumberField
open Module

namespace D1Bound5

/-- The retained coefficient remains greater than one when the first
anchor has modulus only one, for either manuscript interpolation row. -/
theorem _root_.solution
    (A B R lam : ℝ) (hA : 1 ≤ A) (hB : 3 ≤ B) (hR : 0 < R) (hR8 : R ≤ 8)
    (hlam : 0 < lam) (hlam10 : lam ≤ 1/10) :
    1 < (9999/10000 : ℝ)/lam^2 *
      (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2 := by
  have hAB : (9 : ℝ) ≤ A^2*B^2 := by
    calc
      (9 : ℝ) = 1^2*3^2 := by norm_num
      _ ≤ A^2*B^2 := by gcongr <;> first | assumption | norm_num
  have hAB0 : 0 < A^2*B^2 := lt_of_lt_of_le (by norm_num) hAB
  have hinv : (1/8 : ℝ) ≤ 1/R := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8) hR).2
    simpa using hR8
  have herr : (51051/400000 : ℝ)/(A^2*B^2) ≤ (51051/400000)/9 := by
    apply (div_le_div_iff₀ hAB0 (by norm_num : (0 : ℝ) < 9)).2
    nlinarith only [hAB]
  have hd : (11/100 : ℝ) < 1/R-(51051/400000 : ℝ)/(A^2*B^2) := by
    linarith only [hinv,herr]
  have hs : (11/100 : ℝ)^2 < (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2 := by
    have hp := mul_pos (sub_pos.mpr hd)
      (show 0 < (1/R-(51051/400000 : ℝ)/(A^2*B^2))+(11/100) by linarith only [hd])
    nlinarith only [hp]
  have hlamsq : lam^2 ≤ (1/100 : ℝ) := by
    have hh := mul_nonneg (sub_nonneg.mpr hlam10)
      (show 0 ≤ 1/10+lam by positivity)
    nlinarith only [hh]
  have hc : (9999/100 : ℝ) ≤ (9999/10000)/lam^2 := by
    apply (le_div_iff₀ (pow_pos hlam 2)).2
    nlinarith only [hlamsq]
  have hh := mul_le_mul_of_nonneg_right hc
    (sq_nonneg (1/R-(51051/400000 : ℝ)/(A^2*B^2)))
  nlinarith only [hs,hh]



end D1Bound5
end
