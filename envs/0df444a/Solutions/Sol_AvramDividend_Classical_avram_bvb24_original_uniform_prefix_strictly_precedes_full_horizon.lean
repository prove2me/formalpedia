-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb24_original_uniform_prefix_strictly_precedes_full_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:23.875224+00:00
-- url     : https://prove2.me/submissions/9297eded-c8c3-4df1-9253-0d10ed9963cb

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) (n : ℕ) :
    ENNReal.ofReal (T - T / ((n : ℝ) + 2)) <
      ENNReal.ofReal T  := by
  have hDen : 0 < (n : ℝ) + 2 := by positivity
  have hDelta : 0 < T / ((n : ℝ) + 2) := div_pos hT hDen
  exact (ENNReal.ofReal_lt_ofReal_iff hT).2
    (sub_lt_self T hDelta)
