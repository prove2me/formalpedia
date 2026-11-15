-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_half_affine_candidate_strict_interior_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T01:08:18.116586+00:00
-- url     : https://prove2.me/submissions/50a76460-f8e7-4a47-b371-bfbf0eec6960

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
open scoped NNReal ENNReal
theorem solution (C : ℝ≥0∞) :
    ContDiffOn ℝ 1 (fun u : ℝ => if u < 0 then 0 else 1 / 2 + u)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
  have hbase : ContDiff ℝ 1 (fun u : ℝ => (1 / 2 : ℝ) + u) :=
    contDiff_const.add contDiff_id
  apply hbase.contDiffOn.congr
  intro y hy
  have hnot : ¬ y < 0 := not_lt.mpr (le_of_lt hy.1)
  simp [hnot]
