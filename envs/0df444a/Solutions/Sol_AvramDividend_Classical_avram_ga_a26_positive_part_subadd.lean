-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a26_positive_part_subadd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T07:56:46.326093+00:00
-- url     : https://prove2.me/submissions/ac756f04-4325-4a44-9d10-7f96b2eb7a4b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

theorem solution (a b : ℝ) : max (a + b) (0 : ℝ) ≤ max a 0 + max b 0 := by
  apply max_le
  · exact add_le_add (le_max_left _ _) (le_max_left _ _)
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)
