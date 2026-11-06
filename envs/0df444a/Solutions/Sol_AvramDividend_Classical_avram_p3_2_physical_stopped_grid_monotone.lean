-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_physical_stopped_grid_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:53:26.48187+00:00
-- url     : https://prove2.me/submissions/b465f4e7-9195-452f-98c5-651c905744b6

import Mathlib.Data.NNReal.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- The clipped physical uniform time grid remains monotone after
stopping at any finite horizon, including repeated terminal points. -/
theorem solution (T τ : ℝ≥0) (m : ℕ) :
    Monotone (fun j : ℕ =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ) := by
  intro i j hij
  have hnat : min i (m + 1) ≤ min j (m + 1) :=
    min_le_min_right (m + 1) hij
  have hcast : ((min i (m + 1) : ℕ) : ℝ≥0) ≤
      ((min j (m + 1) : ℕ) : ℝ≥0) := by
    exact_mod_cast hnat
  have hmul : ((min i (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1)) ≤
      ((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1)) :=
    mul_le_mul_of_nonneg_right hcast bot_le
  exact min_le_min_right τ hmul
