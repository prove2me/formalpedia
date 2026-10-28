-- Prove2me | solution 1 for AvramDividend.Classical.countable_path_runningSup_increment_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:33:27.209788+00:00
-- url     : https://prove2.me/submissions/277a64e9-ae4e-45f1-a404-e1effddc5f4b

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
theorem solution
    (times : ℕ → ℝ≥0) :
    Measurable (fun f : ℝ≥0 → ℝ =>
      ⨆ n : ℕ, ENNReal.ofReal (f (times n) - f 0)) := by
  refine Measurable.iSup fun n => ?_
  exact ENNReal.measurable_ofReal.comp
    ((measurable_pi_apply (times n)).sub (measurable_pi_apply 0))
