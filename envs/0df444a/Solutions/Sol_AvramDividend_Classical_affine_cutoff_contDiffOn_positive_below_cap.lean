-- Prove2me | solution 1 for AvramDividend.Classical.affine_cutoff_contDiffOn_positive_below_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:33:57.721981+00:00
-- url     : https://prove2.me/submissions/65e7877f-3669-47bf-83fa-280036969b90

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
import Theorems.Thm_AvramDividend_Classical_affine_cutoff_continuous_nonnegative_smooth_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal

theorem solution (C : ℝ≥0∞) :
    ContDiffOn ℝ 2 (fun z : ℝ => if z < 0 then 0 else z - 1)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
  have hsm :=
    (AvramDividend.Classical.affine_cutoff_continuous_nonnegative_smooth_positive).2
  apply hsm.mono
  intro y hy
  exact hy.1
