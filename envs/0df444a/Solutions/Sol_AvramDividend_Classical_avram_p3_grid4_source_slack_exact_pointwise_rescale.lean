-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_source_slack_exact_pointwise_rescale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:39:00.163944+00:00
-- url     : https://prove2.me/submissions/756d6fa8-d45a-4e09-a7d1-dda95059a7b0

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- The strict positive reference value absorbs deterministic grid slack
under one source-faithful nonnegative scalar rescaling. -/
theorem solution
    (w e F Z : ℝ) (hw : 0 < w) (he : 0 ≤ e)
    (hF : F ≤ w + Z + e) :
    (w / (w + e)) * F ≤ w + (w / (w + e)) * Z := by
  have hp : 0 < w + e := add_pos_of_pos_of_nonneg hw he
  have hs : 0 ≤ w / (w + e) := div_nonneg hw.le hp.le
  calc
    (w / (w + e)) * F ≤ (w / (w + e)) * (w + Z + e) :=
      mul_le_mul_of_nonneg_left hF hs
    _ = w + (w / (w + e)) * Z := by
      field_simp [ne_of_gt hp]
      ring
