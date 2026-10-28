-- Prove2me | solution 1 for D1Bound5.coherent_two_scalar_size_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:09.882302+00:00
-- url     : https://prove2.me/submissions/dabc6ee2-1be9-422e-a4bd-3fb59feabd56

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

/-- A denominator-free numerical estimate underlying the two-anchor
nonvanishing argument.  The safe bound `5/4` on the scaled product of
three roots is slightly weaker than its exact square-root value, but
still gives the manuscript's strict constant five. -/
theorem _root_.solution
    (A B P U Q : ℝ)
    (hA : 1 ≤ A) (hB : 3 ≤ B) (hP : 5 * B ≤ P) (hU0 : 0 ≤ U)
    (hU : U ^ 2 ≤ (A * B + 1) * (A * P + 1) * (B * P + 1))
    (hQ : Q ≤ A + B + P + 2 * A * B * P + 2 * U) :
    Q < 5 * A * B * P := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hP15 : 15 ≤ P := by linarith
  have hP0 : 0 < P := by linarith
  have hAB : 3 ≤ A * B := by
    have h := mul_le_mul hA hB (by norm_num : (0 : ℝ) ≤ 3) hA0.le
    nlinarith only [h]
  have hAP : 15 ≤ A * P := by
    have h := mul_le_mul hA hP15 (by norm_num : (0 : ℝ) ≤ 15) hA0.le
    nlinarith only [h]
  have hBP : 45 ≤ B * P := by
    have h := mul_le_mul hB hP15 (by norm_num : (0 : ℝ) ≤ 15) hB0.le
    nlinarith only [h]
  have h1 : A * B + 1 ≤ (4 / 3 : ℝ) * (A * B) := by linarith
  have h2 : A * P + 1 ≤ (16 / 15 : ℝ) * (A * P) := by linarith
  have h3 : B * P + 1 ≤ (46 / 45 : ℝ) * (B * P) := by linarith
  have hprod : (A * B + 1) * (A * P + 1) * (B * P + 1) ≤
      ((4 / 3 : ℝ) * (A * B)) * ((16 / 15 : ℝ) * (A * P)) *
        ((46 / 45 : ℝ) * (B * P)) :=
    mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3
      (by positivity) (by positivity)
  have hscaled : U ^ 2 ≤ (2944 / 2025 : ℝ) * (A * B * P) ^ 2 := by
    calc
      U ^ 2 ≤ (A * B + 1) * (A * P + 1) * (B * P + 1) := hU
      _ ≤ _ := hprod
      _ = (2944 / 2025 : ℝ) * (A * B * P) ^ 2 := by ring
  have hT : 0 < A * B * P := by positivity
  have hUsq : U ^ 2 < ((5 / 4 : ℝ) * (A * B * P)) ^ 2 := by
    nlinarith only [hscaled, sq_pos_of_pos hT]
  have hUbound : U < (5 / 4 : ℝ) * (A * B * P) :=
    (sq_lt_sq₀ hU0 (by positivity)).mp hUsq
  have hAbound : 45 * A ≤ A * B * P := by
    have h := mul_le_mul_of_nonneg_left hBP hA0.le
    nlinarith only [h]
  have hBbound : 15 * B ≤ A * B * P := by
    have h := mul_le_mul_of_nonneg_left hAP hB0.le
    nlinarith only [h]
  have hPbound : 3 * P ≤ A * B * P := by
    have h := mul_le_mul_of_nonneg_right hAB hP0.le
    nlinarith only [h]
  have hsum : A + B + P ≤ (19 / 45 : ℝ) * (A * B * P) := by
    nlinarith only [hAbound, hBbound, hPbound]
  nlinarith only [hQ, hsum, hUbound, hT]









end D1Bound5
end
