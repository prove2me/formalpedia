-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_fourth_exponential_negative_band_uniform_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:01:53.165487+00:00
-- url     : https://prove2.me/submissions/c9baa983-3f44-43eb-b78a-cd5bc7dba541

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- The fourth-exponential jump test has a uniform positive separated-band weight. -/
theorem solution (θ ε y : ℝ) (hθ : 0 < θ) (hε : 0 < ε)
    (hy : y ≤ -ε) :
    (1 - Real.exp (-θ * ε)) ^ 4 ≤ (Real.exp (θ * y) - 1) ^ 4 := by
  have hmul : θ * y ≤ θ * (-ε) :=
    mul_le_mul_of_nonneg_left hy (le_of_lt hθ)
  have hExp : Real.exp (θ * y) ≤ Real.exp (-θ * ε) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hmul]
  have hneg : -θ * ε < 0 := by nlinarith [mul_pos hθ hε]
  have hlt : Real.exp (-θ * ε) < 1 :=
    Real.exp_lt_one_iff.mpr hneg
  have hbase : 0 ≤ 1 - Real.exp (-θ * ε) := by linarith
  have hle : 1 - Real.exp (-θ * ε) ≤ 1 - Real.exp (θ * y) := by
    linarith
  calc
    _ ≤ (1 - Real.exp (θ * y)) ^ 4 := by
      gcongr
    _ = (Real.exp (θ * y) - 1) ^ 4 := by ring
