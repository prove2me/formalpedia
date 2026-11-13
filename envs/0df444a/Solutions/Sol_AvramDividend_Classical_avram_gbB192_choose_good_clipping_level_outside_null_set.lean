-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB192_choose_good_clipping_level_outside_null_set
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T19:18:11.042965+00:00
-- url     : https://prove2.me/submissions/d7212c15-e2b4-47f4-b51f-9c5f56c092b5

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution
    (S : Set ℝ) (hS : (volume : Measure ℝ) S = 0)
    (a b : ℝ) (hab : a < b) :
    ∃ z : ℝ, z ∈ Ioo a b ∧ z ∉ S := by
  by_contra h
  push_neg at h
  have hsub : Ioo a b ⊆ S := by
    intro z hz
    exact h z hz
  have hle : (volume : Measure ℝ) (Ioo a b) ≤
      (volume : Measure ℝ) S := measure_mono hsub
  rw [hS] at hle
  have hpos : (0 : ℝ≥0∞) < (volume : Measure ℝ) (Ioo a b) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  exact (not_le_of_gt hpos) hle
