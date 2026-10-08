-- Prove2me | solution 1 for AvramDividend.Classical.exponential_dividend_lump_sum_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:20:17.103049+00:00
-- url     : https://prove2.me/submissions/26bbdda4-0460-484c-91ab-860d456cb728

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

theorem solution
    (θ u d : ℝ) (hθ : 1 ≤ θ) (hu : 0 ≤ u) (hd : 0 ≤ d) :
    d ≤ Real.exp (θ * (u + d)) - Real.exp (θ * u) := by
  have hθzero : 0 ≤ θ := le_trans zero_le_one hθ
  have heBase : 1 ≤ Real.exp (θ * u) :=
    Real.one_le_exp (mul_nonneg hθzero hu)
  have hePay : 1 ≤ Real.exp (θ * d) :=
    Real.one_le_exp (mul_nonneg hθzero hd)
  have hnonneg : 0 ≤ Real.exp (θ * d) - 1 :=
    sub_nonneg.mpr hePay
  have htheta : d ≤ θ * d := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hθ hd
  have hGap : d ≤ Real.exp (θ * d) - 1 := by
    have h := Real.add_one_le_exp (θ * d)
    linarith
  calc
    d ≤ Real.exp (θ * d) - 1 := hGap
    _ = 1 * (Real.exp (θ * d) - 1) := by ring
    _ ≤ Real.exp (θ * u) * (Real.exp (θ * d) - 1) :=
      mul_le_mul_of_nonneg_right heBase hnonneg
    _ = Real.exp (θ * (u + d)) - Real.exp (θ * u) := by
      rw [mul_add, Real.exp_add]
      ring
