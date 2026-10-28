-- Prove2me | solution 1 for D1Bound5.coherent_two_main_size_parameters
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:53.703992+00:00
-- url     : https://prove2.me/submissions/5904282e-625c-4e1e-bc77-de2c529b36fa

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
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

/-- The two main size regimes already imply the analytic parameter
conditions used by the strong two-anchor gap. -/
theorem _root_.solution
    (A B P Q : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) (hB : 3 ≤ B)
    (hP : 5 * B ≤ P) (hQ : 5 * A * B * P ≤ Q)
    (hlarge : 3 ≤ A ∨ 48 ≤ P) :
    32 ≤ A * P ∧ 10000 < P * Q := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hP15 : 15 ≤ P := by linarith
  have hP0 : 0 < P := by linarith
  have hPQ : 5 * (A * B) * P ^ 2 ≤ P * Q := by
    have h := mul_le_mul_of_nonneg_left hQ hP0.le
    nlinarith only [h]
  rcases hlarge with hA3 | hP48
  · have hAP45 : 45 ≤ A * P := by
      have h := mul_le_mul hA3 hP15 (by norm_num : (0 : ℝ) ≤ 15) hA0.le
      nlinarith only [h]
    have hAB9 : 9 ≤ A * B := by
      have h := mul_le_mul hA3 hB (by norm_num : (0 : ℝ) ≤ 3) hA0.le
      nlinarith only [h]
    have hP225 : 225 ≤ P ^ 2 := by nlinarith only [hP15, sq_nonneg (P-15)]
    have hprod := mul_le_mul hAB9 hP225 (by norm_num : (0 : ℝ) ≤ 225)
      (by positivity : 0 ≤ A * B)
    exact ⟨by linarith, by nlinarith only [hPQ, hprod]⟩
  · have hAP48 : 48 ≤ A * P := by
      have h := mul_le_mul hA hP48 (by norm_num : (0 : ℝ) ≤ 48) hA0.le
      nlinarith only [h]
    have hAB3 : 3 ≤ A * B := by
      have h := mul_le_mul hA hB (by norm_num : (0 : ℝ) ≤ 3) hA0.le
      nlinarith only [h]
    have hP2304 : 2304 ≤ P ^ 2 := by nlinarith only [hP48, sq_nonneg (P-48)]
    have hprod := mul_le_mul hAB3 hP2304 (by norm_num : (0 : ℝ) ≤ 2304)
      (by positivity : 0 ≤ A * B)
    exact ⟨by linarith, by nlinarith only [hPQ, hprod]⟩



end D1Bound5
end
