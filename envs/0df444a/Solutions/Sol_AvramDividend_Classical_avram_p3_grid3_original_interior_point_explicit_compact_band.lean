-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_interior_point_explicit_compact_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:18:12.944708+00:00
-- url     : https://prove2.me/submissions/64399a83-f42e-465f-8e51-6b62a6dfa297

import Mathlib.Data.ENNReal.Real
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (y : ℝ) (hy : 0 < y)
    (hyC : ENNReal.ofReal y < C) :
    let a : ℝ := min 1 y
    let b : ℝ := y
    0 < a ∧ a ≤ 2 ∧ a ≤ b ∧ y ∈ Set.Icc a b ∧
      Set.Icc (a / 2) b ⊆
        {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} := by
  dsimp
  have ha : 0 < min (1 : ℝ) y := lt_min (by norm_num) hy
  refine ⟨ha, ?_, min_le_right (1 : ℝ) y, ⟨min_le_right (1 : ℝ) y, le_rfl⟩, ?_⟩
  · calc
      min (1 : ℝ) y ≤ 1 := min_le_left (1 : ℝ) y
      _ ≤ 2 := by norm_num
  · intro z hz
    have hzpos : 0 < z := by
      have hhalf : 0 < min (1 : ℝ) y / 2 := half_pos ha
      exact lt_of_lt_of_le hhalf hz.1
    exact ⟨hzpos, lt_of_le_of_lt (ENNReal.ofReal_mono hz.2) hyC⟩
