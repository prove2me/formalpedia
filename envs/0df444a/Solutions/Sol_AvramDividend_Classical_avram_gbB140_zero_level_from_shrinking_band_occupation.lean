-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB140_zero_level_from_shrinking_band_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T09:37:12.325307+00:00
-- url     : https://prove2.me/submissions/dd1af26c-ef78-435f-88de-ba74b0615ee7

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (x : ℝ≥0∞) (u : ℕ → ℝ≥0∞)
    (hbound : ∀ k, x ≤ u k)
    (hlim : Tendsto u atTop (𝓝 (0 : ℝ≥0∞))) :
    x = 0 := by
  apply le_antisymm ?_ bot_le
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
