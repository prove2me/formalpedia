-- Prove2me | solution 1 for AvramDividend.Classical.ennreal_scale_ratio_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:41:26.700794+00:00
-- url     : https://prove2.me/submissions/57f03106-04f5-4e9d-a3f0-191526d12c64

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    (x a d : ℝ) (hx : 0 ≤ x) (ha : 0 < a) (hd : 0 < d) :
    ENNReal.ofReal (x / a) * ENNReal.ofReal (a / d) =
      ENNReal.ofReal (x / d) := by
  have hxa : 0 ≤ x / a := div_nonneg hx (le_of_lt ha)
  rw [← ENNReal.ofReal_mul hxa]
  congr 1
  field_simp [ne_of_gt ha, ne_of_gt hd]
