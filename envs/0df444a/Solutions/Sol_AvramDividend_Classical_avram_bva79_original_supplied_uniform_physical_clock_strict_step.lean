-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva79_original_supplied_uniform_physical_clock_strict_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:11:01.698942+00:00
-- url     : https://prove2.me/submissions/b30c805a-b97a-431f-a028-2ec76325d248

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ n i : ℕ, u n i < u n (i + 1) := by
  intro n i
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hstep : 0 < T / ((n : ℝ) + 2) := div_pos hT hden
  have hreal : (u n i : ℝ) < (u n (i + 1) : ℝ) := by
    rw [huniform n i, huniform n (i + 1)]
    push_cast
    have hsum :
        T * ((i : ℝ) + 1) / ((n : ℝ) + 2) =
          T * (i : ℝ) / ((n : ℝ) + 2) + T / ((n : ℝ) + 2) := by ring
    rw [hsum]
    linarith
  exact_mod_cast hreal
