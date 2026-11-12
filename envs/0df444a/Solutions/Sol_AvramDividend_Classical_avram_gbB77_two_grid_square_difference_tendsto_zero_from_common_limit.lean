-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB77_two_grid_square_difference_tendsto_zero_from_common_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:04:18.282201+00:00
-- url     : https://prove2.me/submissions/d4af8bf5-3133-4fff-b109-223e84826f71

import Mathlib
open Filter Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem solution (f : ℕ → ℝ) (a : ℝ)
    (hf : Tendsto f atTop (𝓝 a)) :
    Tendsto (fun nm : ℕ × ℕ => (f nm.1 - f nm.2) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
  have hfst : Tendsto (fun nm : ℕ × ℕ => nm.1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop (b, 0)] with nm hnm
    exact hnm.1
  have hsnd : Tendsto (fun nm : ℕ × ℕ => nm.2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop (0, b)] with nm hnm
    exact hnm.2
  have hdiff : Tendsto (fun nm : ℕ × ℕ => f nm.1 - f nm.2)
      atTop (𝓝 (a - a)) := (hf.comp hfst).sub (hf.comp hsnd)
  simpa using hdiff.pow 2
