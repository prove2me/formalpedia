-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a183_drift_shift_large_raw_square_tail_le_centered_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:53:16.393678+00:00
-- url     : https://prove2.me/submissions/3eed9fc8-98e2-40cb-bfc6-310e57fab5ca

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section

/-- Large physical raw increments are controlled by large drift-centred
increments when the deterministic drift displacement is small. -/
theorem solution
    (z d δ : ℝ) (hδ : 0 < δ) (hd : |d| ≤ δ / 2) :
    (if δ ≤ |z + d| then (z + d)^2 else 0) ≤
      4 * (if δ / 2 ≤ |z| then z^2 else 0) := by
  by_cases hraw : δ ≤ |z + d|
  · have hz : δ / 2 ≤ |z| := by
      have htri := abs_add_le z d
      linarith
    simp only [if_pos hraw, if_pos hz]
    have hdd : |d| ≤ |z| := hd.trans hz
    have hrawBound : |z + d| ≤ 2 * |z| := by
      have htri := abs_add_le z d
      linarith
    have hsquare : |z + d|^2 ≤ (2 * |z|)^2 := by
      nlinarith [mul_nonneg
        (sub_nonneg.mpr hrawBound)
        (add_nonneg (abs_nonneg (z+d)) (by positivity : 0 ≤ 2 * |z|))]
    nlinarith [sq_abs (z + d), sq_abs z]
  · simp only [if_neg hraw]
    positivity
