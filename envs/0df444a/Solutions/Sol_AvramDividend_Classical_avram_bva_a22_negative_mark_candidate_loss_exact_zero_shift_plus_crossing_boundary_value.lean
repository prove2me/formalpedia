-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_negative_mark_candidate_loss_exact_zero_shift_plus_crossing_boundary_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:55:47.05248+00:00
-- url     : https://prove2.me/submissions/ea87cf97-72a9-458a-b061-3a314c75554e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical Set Filter AvramDividend.Classical
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (y z : ℝ) (hy : 0 < y) (hz : z < 0) :
    w y - w (y + z) =
      ((w y - w 0) -
        (if y + z < 0 then 0 else w (y + z) - w 0)) +
      (if y + z < 0 then w 0 else 0) := by
  by_cases h : y + z < 0
  · simp only [if_pos h, hw_neg (y + z) h, sub_zero]
    ring
  · simp only [if_neg h, add_zero]
    ring
