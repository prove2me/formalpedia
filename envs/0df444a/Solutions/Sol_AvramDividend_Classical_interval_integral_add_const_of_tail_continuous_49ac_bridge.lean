-- Prove2me | solution 1 for AvramDividend.Classical.interval_integral_add_const_of_tail_continuous_49ac_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:05:21.061043+00:00
-- url     : https://prove2.me/submissions/b05d3e2c-2ccd-482e-8d72-f98687f54e16

import Mathlib
open MeasureTheory Set Topology
open scoped NNReal ENNReal
theorem solution
    (φ : ℝ) (tail : ℝ → ℝ) (a b : ℝ)
    (hTail : ContinuousOn tail (Ioi (0 : ℝ)))
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, φ + tail t) = φ * (b - a) + (∫ t in a..b, tail t) := by
  have hsub : Set.uIcc a b ⊆ Ioi (0 : ℝ) := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  have h1 : IntervalIntegrable tail volume a b := (hTail.mono hsub).intervalIntegrable
  rw [intervalIntegral.integral_add intervalIntegrable_const h1]
  simp
  ring
