-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_expMeasure_strict_survival_positive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T01:01:12.362356+00:00
-- url     : https://prove2.me/submissions/fd2ea3fc-ed29-4051-9a78-1d2a31cc9eb8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal


theorem solution (p a : ℝ) (hp : 0 < p) (ha : 0 ≤ a) :
    0 < ProbabilityTheory.expMeasure p (Set.Ioi a) := by
  rw [avram_ws01e_b_expMeasure_strict_survival_real p a hp ha]
  exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
