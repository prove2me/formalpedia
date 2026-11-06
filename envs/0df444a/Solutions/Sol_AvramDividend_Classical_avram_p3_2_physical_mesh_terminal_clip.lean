-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_physical_mesh_terminal_clip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:23:22.567286+00:00
-- url     : https://prove2.me/submissions/7ce6a1ef-bbbb-4f4d-9be7-17b796b2cb58

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- The final physical grid point is exactly the stopped clock. -/
theorem solution (T τ : ℝ≥0) (m : ℕ) (hτ : τ ≤ T) :
    min (((min (m + 1) (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ = τ := by
  have hn : (m : ℝ≥0) + 1 ≠ 0 := by positivity
  have hmul : ((m : ℝ≥0) + 1) * (T / ((m : ℝ≥0) + 1)) = T := by
    field_simp [hn]
  calc
    _ = min T τ := by
      simp only [min_self, Nat.cast_add, Nat.cast_one, hmul]
    _ = τ := min_eq_right hτ
