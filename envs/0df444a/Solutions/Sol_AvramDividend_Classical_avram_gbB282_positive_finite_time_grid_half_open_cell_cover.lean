-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB282_positive_finite_time_grid_half_open_cell_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:58:21.048205+00:00
-- url     : https://prove2.me/submissions/a846c781-2439-4452-866b-efd38d66376c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

/-- A finite positive real mesh covers its half-open physical-time horizon. -/
theorem solution (N : ℕ) (δ t : ℝ)
    (hδ : 0 < δ) (ht : 0 ≤ t) (horizon : t < (N : ℝ) * δ) :
    ∃ i : ℕ, i < N ∧
      (i : ℝ) * δ ≤ t ∧ t < ((i : ℝ) + 1) * δ := by
  revert horizon
  induction N with
  | zero =>
      intro horizon
      norm_num at horizon
      linarith
  | succ N ih =>
      intro horizon
      have hlast : t < ((N : ℝ) + 1) * δ := by
        simpa only [Nat.cast_add, Nat.cast_one] using horizon
      by_cases hprev : t < (N : ℝ) * δ
      · obtain ⟨i, hi, hL, hU⟩ := ih hprev
        exact ⟨i, Nat.lt_succ_of_lt hi, hL, hU⟩
      · exact ⟨N, Nat.lt_succ_self N, le_of_not_gt hprev, hlast⟩
