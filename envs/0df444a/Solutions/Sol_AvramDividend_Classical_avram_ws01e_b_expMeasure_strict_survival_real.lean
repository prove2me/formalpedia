-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_expMeasure_strict_survival_real
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:54:52.940926+00:00
-- url     : https://prove2.me/submissions/d710f9aa-410f-417a-9420-47d78a32b22c

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.CDF
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem solution
    (p a : ℝ) (hp : 0 < p) (ha : 0 ≤ a) :
    ProbabilityTheory.expMeasure p (Set.Ioi a) =
      ENNReal.ofReal (Real.exp (-(p * a))) := by
  have := isProbabilityMeasure_expMeasure hp
  rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf,
    cdf_expMeasure_eq hp, if_pos ha, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (by
      have : Real.exp (-(p * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      linarith)]
  congr 1; ring
