-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01e_b_exp_clock_toNNReal_strict_tail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:59:09.085478+00:00
-- url     : https://prove2.me/submissions/7010ca9b-2ea6-47f3-91b8-df7283f25816

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal


theorem solution (p : ℝ) (hp : 0 < p) (a : ℝ≥0) :
    expMeasure p {t : ℝ | a < t.toNNReal} =
      ENNReal.ofReal (Real.exp (-(p * (a : ℝ)))) := by
  have h : {t : ℝ | a < t.toNNReal} = Set.Ioi (a : ℝ) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Ioi]
    exact Real.lt_toNNReal_iff_coe_lt
  rw [h]
  exact avram_ws01e_b_expMeasure_strict_survival_real p a hp a.2
