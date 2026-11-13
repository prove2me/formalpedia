-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a27_prehorizon_grid_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:55:48.183276+00:00
-- url     : https://prove2.me/submissions/6f8f28c2-a943-43b0-a3bb-8cf3c4ec1c7a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

theorem solution (n : ℝ≥0) (m : ℕ) :
    (m : ℝ≥0) * (n / ((m : ℝ≥0) + 1)) ≤ n := by
  have hm : (m : ℝ≥0) ≤ (m : ℝ≥0) + 1 := by simp
  have hmul : (m : ℝ≥0) * n ≤ n * ((m : ℝ≥0) + 1) := by
    calc
      (m : ℝ≥0) * n ≤ ((m : ℝ≥0) + 1) * n :=
        mul_le_mul_of_nonneg_right hm (by positivity)
      _ = n * ((m : ℝ≥0) + 1) := mul_comm _ _
  have hd : (0 : ℝ≥0) < (m : ℝ≥0) + 1 := by positivity
  calc
    (m : ℝ≥0) * (n / ((m : ℝ≥0) + 1)) =
        ((m : ℝ≥0) * n) / ((m : ℝ≥0) + 1) := by rw [mul_div_assoc]
    _ ≤ n := (div_le_iff₀ hd).mpr hmul
