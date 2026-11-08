-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_ruin8_nonnegative_ruin_clip_contact_increment_le_raw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:17:34.740905+00:00
-- url     : https://prove2.me/submissions/c042a708-dd68-4899-bed0-e134a457234b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- Clipping a stopped ruin-contact reserve at zero cannot enlarge the
absolute compensated physical-cell increment from a nonnegative reserve. -/
theorem solution (z c : ℝ) (hz : 0 ≤ z) :
    |max (z + c) 0 - z| ≤ |c| := by
  rcases le_total (z + c) 0 with hneg | hpos
  · rw [max_eq_right hneg]
    have hc : c ≤ 0 := by linarith
    rw [abs_of_nonpos (by linarith : 0 - z ≤ 0), abs_of_nonpos hc]
    linarith
  · rw [max_eq_left hpos]
    have heq : z + c - z = c := by ring
    rw [heq]
