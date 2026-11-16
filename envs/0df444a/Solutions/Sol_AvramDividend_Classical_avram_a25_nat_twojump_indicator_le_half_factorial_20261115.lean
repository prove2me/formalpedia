-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_nat_twojump_indicator_le_half_factorial_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:03:12.058841+00:00
-- url     : https://prove2.me/submissions/0c1c726a-ea4a-46cd-a1a6-408b20ee3bbe

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- Counting at least two physical jumps costs one unordered pair. -/
theorem solution (k : ℕ) :
    (if 2 ≤ k then (1 : ℝ) else 0) ≤
      ((k : ℝ) * ((k : ℝ) - 1)) / 2 := by
  by_cases hk : 2 ≤ k
  · simp only [if_pos hk]
    have hR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hp : 0 ≤ ((k : ℝ) - 1) * ((k : ℝ) - 2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · have hs : k = 0 ∨ k = 1 := by omega
    rcases hs with rfl | rfl
    · norm_num
    · norm_num
