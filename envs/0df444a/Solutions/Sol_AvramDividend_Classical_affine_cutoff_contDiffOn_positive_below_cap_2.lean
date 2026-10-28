-- Prove2me | solution 2 for AvramDividend.Classical.affine_cutoff_contDiffOn_positive_below_cap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:33:58.416393+00:00
-- url     : https://prove2.me/submissions/b0dd3451-aa35-4a81-93e9-15858a1f8333

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
import Theorems.Thm_AvramDividend_Classical_affine_cutoff_continuous_nonnegative_smooth_positive
open Set
open scoped ENNReal
theorem solution (C : ℝ≥0∞) :
    ContDiffOn ℝ 2 (fun z : ℝ => if z < 0 then 0 else z - 1)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
  refine ((contDiff_id.sub (contDiff_const (c := (1:ℝ)))).contDiffOn (s := {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})).congr ?_
  intro y hy
  simp [not_lt.mpr hy.1.le]
