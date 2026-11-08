-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_affine_zero_extension_smooth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:28:40.233906+00:00
-- url     : https://prove2.me/submissions/7bed616e-7648-496e-b01d-7cba7c422969

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal

/-- The zero-extended affine function is smooth throughout the positive generator domain. -/
theorem solution (C : ℝ≥0∞) :
    ContDiffOn ℝ 1
      (fun y : ℝ => if y < 0 then (0 : ℝ) else 1 + y)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
  have haffine : ContDiff ℝ 1 (fun y : ℝ => 1 + y) :=
    contDiff_const.add contDiff_id
  apply haffine.contDiffOn.congr
  intro y hy
  simp [not_lt.mpr (le_of_lt hy.1)]
