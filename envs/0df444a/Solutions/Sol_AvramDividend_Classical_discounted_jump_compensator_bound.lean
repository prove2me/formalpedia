-- Prove2me | solution 1 for AvramDividend.Classical.discounted_jump_compensator_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T21:56:00.741985+00:00
-- url     : https://prove2.me/submissions/2c0db4b1-8360-4a25-a1e0-b74c3396cc66

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (θ z : ℝ) (hθ : 1 ≤ θ) (hz : 0 ≤ z) :
    0 ≤ (1 - Real.exp (-θ * z)) / θ ∧
      (1 - Real.exp (-θ * z)) / θ ≤ min z 1 := by
  have hθpos : 0 < θ := lt_of_lt_of_le (by norm_num) hθ
  have hprod : 0 ≤ θ * z := mul_nonneg hθpos.le hz
  have hexp : Real.exp (-θ * z) ≤ 1 := by
    have h := Real.exp_le_exp.mpr (show -θ * z ≤ 0 by nlinarith)
    simpa using h
  constructor
  · exact div_nonneg (sub_nonneg.mpr hexp) hθpos.le
  · apply le_min
    · rw [div_le_iff₀ hθpos]
      have h := Real.add_one_le_exp (-θ * z)
      nlinarith
    · rw [div_le_iff₀ hθpos]
      have h := Real.exp_pos (-θ * z)
      nlinarith
