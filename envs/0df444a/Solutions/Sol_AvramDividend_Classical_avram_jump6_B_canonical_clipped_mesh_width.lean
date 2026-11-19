-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_canonical_clipped_mesh_width
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:35:43.508209+00:00
-- url     : https://prove2.me/submissions/9e356486-b1f2-4d3a-9d12-cb68c5e85641

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

theorem solution
    (j i : ℕ) (t : ℝ≥0) :
    min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t ≤
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t +
        (1 : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) := by
  have hdiv :
      (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) =
        ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) +
          (1 : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) := by
    simp only [Nat.cast_add, Nat.cast_one, add_div]
  rw [hdiv]
  rcases le_total ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t with h | h
  · rw [min_eq_left h]
    exact min_le_left _ _
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (le_add_of_nonneg_right (by positivity))
