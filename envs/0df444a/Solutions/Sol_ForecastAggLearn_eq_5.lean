-- Prove2me | solution 1 for ForecastAggLearn.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-11T12:07:02.37054+00:00
-- url     : https://prove2.me/submissions/f634f4af-fef8-455d-8930-2385990ad2ba

import Definitions.Def_ForecastAggLearn_barL
import Mathlib.Tactic.Ring

open ForecastAggLearn
set_option linter.unusedVariables false

theorem solution {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (μt : ℝ) (h : EuclideanSpace ℝ (Fin n))
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    q * barL z μt true h + (1 - q) * barL z μt false h =
      -(q - 1) * (inner ℝ h z + μt) + Real.log (1 + Real.exp (-(inner ℝ h z + μt))) := by
  simp only [barL, Bool.false_eq_true, if_false, if_true, zero_mul, one_mul, zero_add]
  rw [neg_add]
  ring

#print axioms solution
