-- Prove2me | solution 1 for BroughanRH.lagarias
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:47:38.428768+00:00
-- url     : https://prove2.me/submissions/76de4adb-8daf-474b-b7a7-774ad441e0b0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BroughanRH_robin
import Theorems.Thm_LeanEval_NumberTheory_lagarias_harmonic_lower_bound
import Theorems.Thm_LeanEval_NumberTheory_lagarias_finite_range
import Mathlib

theorem solution :
    ∀ n : ℕ, 0 < n → ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  intro n hn
  rcases le_or_gt n 5040 with h | h
  · exact (LeanEval.NumberTheory.lagarias_finite_range n hn h).1
  · have h1 := BroughanRH.robin n h
    have h2 := LeanEval.NumberTheory.lagarias_harmonic_lower_bound n (by omega)
    have h3 : (0 : ℝ) ≤ (harmonic n : ℝ) := by exact_mod_cast (harmonic_pos (by omega)).le
    linarith
