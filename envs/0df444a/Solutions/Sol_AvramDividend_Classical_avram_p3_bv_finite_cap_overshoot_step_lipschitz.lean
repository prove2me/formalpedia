-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_finite_cap_overshoot_step_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:20:54.436322+00:00
-- url     : https://prove2.me/submissions/1602b5bf-dce3-4044-b586-7132c6d008f9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/- The finite-cap overshoot map is 1-Lipschitz across every frozen original
source increment, even one crossing the cap in either direction. -/
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (c z d : ℝ) :
    |max (z + d - c) 0 - max (z - c) 0| ≤ |d| := by
  have hminus : -|d| ≤ d := neg_abs_le d
  have hplus : d ≤ |d| := le_abs_self d
  have habs : ∀ r : ℝ, (-|d| ≤ r ∧ r ≤ |d|) → |r| ≤ |d| := by
    intro r hr
    exact abs_le.mpr hr
  rcases le_total (z + d - c) 0 with hA | hA
  · rcases le_total (z - c) 0 with hB | hB
    · rw [max_eq_right hA, max_eq_right hB]
      simpa using (abs_nonneg d)
    · rw [max_eq_right hA, max_eq_left hB]
      apply habs
      constructor <;> linarith only [hA, hB, hminus, hplus]
  · rcases le_total (z - c) 0 with hB | hB
    · rw [max_eq_left hA, max_eq_right hB]
      apply habs
      constructor <;> linarith only [hA, hB, hminus, hplus]
    · rw [max_eq_left hA, max_eq_left hB]
      apply habs
      constructor <;> linarith only [hminus, hplus]
