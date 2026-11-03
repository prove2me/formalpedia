-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_source_grid_left_window_limit_for_random_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:05:13.954321+00:00
-- url     : https://prove2.me/submissions/234d0ba0-662f-4976-a25b-37cc253baad6

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Saturated left windows on the original nonnegative clock converge
to the candidate positive jump time as their radii vanish. -/
theorem solution
    (t : ℝ≥0) (ε : ℕ → ℝ≥0)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => t - ε n) atTop (𝓝 t) := by
  simpa only [tsub_zero] using (tendsto_const_nhds.sub hε)
