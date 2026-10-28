-- Prove2me | solution 1 for D1Bound5.growth_quadratic_negative
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:25:39.258024+00:00
-- url     : https://prove2.me/submissions/a422f88d-7db5-4ff6-b78a-31bf69777992

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_monic_quadratic_neg_between

section
open scoped NumberField
open Module

namespace D1Bound5







/-- Exact real endpoint estimates behind Lemma irregular-growth. -/
theorem _root_.solution (A B C : ℝ) (hA : 3 ≤ A) (hAB : A ≤ B)
    (hBC : B ≤ C) (hC : C ≤ 2*A*B) :
    (A+B+C+1)^2+4-4*A*B*C < 0 := by
  have hB : 3 ≤ B := hA.trans hAB
  have hAa := mul_le_mul_of_nonneg_left hB (by linarith : 0 ≤ A)
  have hBb := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ B)
  have h9 : 9 ≤ A*B := by nlinarith only [hBb, hB]
  have hS : 9*(A+B+1) ≤ 7*A*B := by nlinarith only [hAa, hBb, h9]
  have hB2 : 9 ≤ B^2 := by nlinarith [sq_nonneg (B-3)]
  have hAB2 : 81 ≤ (A*B)^2 := by nlinarith [sq_nonneg (A*B-9)]
  have hleft : (A+B+B+1)^2+4-4*A*B*B < 0 := by
    have hbnd : 3*(A+2*B+1) ≤ 10*B := by linarith
    have hsq := mul_nonneg (sub_nonneg.mpr hbnd)
      (show 0 ≤ 10*B+3*(A+2*B+1) by linarith)
    have hABsq := mul_le_mul_of_nonneg_right hA (sq_nonneg B)
    nlinarith only [hsq, hABsq, hB2]
  have hright : (A+B+2*A*B+1)^2+4-4*A*B*(2*A*B) < 0 := by
    have hbnd : 9*(A+B+2*A*B+1) ≤ 25*A*B := by nlinarith only [hS]
    have hsq := mul_nonneg (sub_nonneg.mpr hbnd)
      (show 0 ≤ 25*A*B+9*(A+B+2*A*B+1) by nlinarith only [h9, hA, hB])
    nlinarith only [hsq, hAB2]
  have hlu : B < 2*A*B := by nlinarith only [hBb, hB]
  have h := monic_quadratic_neg_between B (2*A*B) C (2*(A+B+1)-4*A*B)
    ((A+B+1)^2+4) hlu hBC hC (by nlinarith only [hleft]) (by nlinarith only [hright])
  nlinarith only [h]





end D1Bound5
end
