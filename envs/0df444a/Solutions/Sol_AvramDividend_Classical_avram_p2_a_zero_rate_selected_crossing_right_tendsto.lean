-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_selected_crossing_right_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:38:52.066879+00:00
-- url     : https://prove2.me/submissions/949d3773-ce59-41ca-9191-4b8e241fbaa0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_selected_right_endpoint_squeeze
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Right endpoints of shrinking source cells that cross a fixed genuine
jump time converge to that jump time. -/
theorem solution
    (u : ℝ≥0) (a b w : ℕ → ℝ≥0)
    (hcell : ∀ n, a n < u ∧ u ≤ b n)
    (hbw : ∀ n, b n ≤ a n + w n)
    (hw : Tendsto w atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto b atTop (𝓝 u) := by
  apply avram_p2_a_zero_rate_selected_right_endpoint_squeeze u b w
  · intro n
    refine ⟨(hcell n).2, ?_⟩
    calc
      b n ≤ a n + w n := hbw n
      _ ≤ u + w n := add_le_add_left (le_of_lt (hcell n).1) (w n)
  · exact hw
