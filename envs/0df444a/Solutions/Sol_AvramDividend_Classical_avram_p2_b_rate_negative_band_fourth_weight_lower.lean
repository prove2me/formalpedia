-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_negative_band_fourth_weight_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:29:53.149731+00:00
-- url     : https://prove2.me/submissions/64192f84-abae-4171-8f96-6d8120f5e472

import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real

theorem solution
    (θ ε y : ℝ) (hθ : 0 < θ) (hε : 0 < ε) (hy : y ≤ -ε) :
    (1 - Real.exp (-θ * ε)) ^ 4 ≤
      (Real.exp (θ * y) - 1) ^ 4 := by
  have hmul : θ * y ≤ -θ * ε := by
    calc
      θ * y ≤ θ * (-ε) := mul_le_mul_of_nonneg_left hy (le_of_lt hθ)
      _ = -θ * ε := by ring
  have hexp : Real.exp (θ * y) ≤ Real.exp (-θ * ε) :=
    Real.exp_le_exp.mpr hmul
  have hbase : 0 ≤ 1 - Real.exp (-θ * ε) := by
    have hneg : -θ * ε ≤ 0 := by nlinarith [mul_pos hθ hε]
    have hle : Real.exp (-θ * ε) ≤ 1 := Real.exp_le_one_iff.mpr hneg
    linarith
  have hdiff : 1 - Real.exp (-θ * ε) ≤ 1 - Real.exp (θ * y) := by
    linarith
  calc
    (1 - Real.exp (-θ * ε)) ^ 4 ≤
        (1 - Real.exp (θ * y)) ^ 4 :=
      pow_le_pow_left₀ hbase hdiff 4
    _ = (Real.exp (θ * y) - 1) ^ 4 := by ring