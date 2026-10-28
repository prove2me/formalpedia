-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_exp_clock_toNNReal_strict_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T00:58:49.767082+00:00
-- url     : https://prove2.me/submissions/2bea96fc-3d79-4489-a4ec-6bb319a2a063

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution (p : ℝ) (hp : 0 < p) (a : ℝ≥0) :
    expMeasure p {t : ℝ | a < t.toNNReal} =
      ENNReal.ofReal (Real.exp (-(p * (a : ℝ)))) := by
  have hset : {t : ℝ | a < t.toNNReal} = Set.Ioi (a : ℝ) := by
    ext t
    exact Real.lt_toNNReal_iff_coe_lt
  rw [hset]
  exact avram_ws01e_b_expMeasure_strict_survival_real
    p (a : ℝ) hp a.property
