-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger123_clipped_uniform_grid_reaches_stop_by_final_index
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:48:47.503338+00:00
-- url     : https://prove2.me/submissions/03f6a949-7cf9-43da-90b9-cb6f38b74b5b

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section

/-- At the final uniform mesh index the original clipped grid equals its stop. -/
theorem solution (n m : ℕ) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    v (m + 2) = ρ := by
  dsimp
  have hden : ((m : ℝ≥0) + 2) ≠ 0 := by positivity
  have hcast : (((m + 2 : ℕ) : ℝ≥0)) = (m : ℝ≥0) + 2 := by
    push_cast
    ring
  rw [hcast]
  have hmul : ((m : ℝ≥0) + 2) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 2)) = (n : ℝ≥0) := by
    field_simp [hden]
  rw [hmul]
  exact min_eq_right hρn
