-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_exponential_nnreal_survival_memorylessness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:55:04.58228+00:00
-- url     : https://prove2.me/submissions/05dcd80a-8703-40bc-8b6b-38f8803d598b

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

open scoped NNReal ENNReal

/-- The authentic exponential-clock strict-survival kernel is memoryless
for all nonnegative stopping ages and increments. The ENNReal factors are
finite, positive real exponentials; no divergent expectation is involved. -/

theorem solution
    (p : ℝ) (hp : 0 < p) (a t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-(p * ((a + t : ℝ≥0) : ℝ)))) =
      ENNReal.ofReal (Real.exp (-(p * (t : ℝ)))) *
        ENNReal.ofReal (Real.exp (-(p * (a : ℝ)))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  push_cast
  ring
