-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_negative_band_weight_uniform_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:45:32.608994+00:00
-- url     : https://prove2.me/submissions/791d6f96-efe1-41a7-a9cb-b5078c786dd9

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (θ ε y : ℝ) (hθ : 0 < θ) (hε : 0 < ε) (hy : y ≤ -ε) :
    0 < (1 - Real.exp (-(θ * ε))) ^ 4 ∧
      (1 - Real.exp (-(θ * ε))) ^ 4 ≤
        (Real.exp (θ * y) - 1) ^ 4 := by
  have hθε : 0 < θ * ε := mul_pos hθ hε
  have hneg : -(θ * ε) < 0 := by linarith
  have hexp_lt : Real.exp (-(θ * ε)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hneg
  have hbase : 0 < 1 - Real.exp (-(θ * ε)) := by linarith
  have hyθ : θ * y ≤ -(θ * ε) := by
    nlinarith [mul_le_mul_of_nonneg_left hy (le_of_lt hθ)]
  have hexp_le : Real.exp (θ * y) ≤ Real.exp (-(θ * ε)) :=
    Real.exp_le_exp.mpr hyθ
  have hsmall : 1 - Real.exp (-(θ * ε)) ≤ 1 - Real.exp (θ * y) := by
    linarith
  constructor
  · positivity
  · calc
      (1 - Real.exp (-(θ * ε))) ^ 4 ≤
          (1 - Real.exp (θ * y)) ^ 4 := by
            gcongr
      _ = (Real.exp (θ * y) - 1) ^ 4 := by ring
