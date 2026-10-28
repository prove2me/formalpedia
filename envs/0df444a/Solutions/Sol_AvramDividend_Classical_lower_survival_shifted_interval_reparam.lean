-- Prove2me | solution 1 for AvramDividend.Classical.lower_survival_shifted_interval_reparam
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:01:05.822673+00:00
-- url     : https://prove2.me/submissions/72a60c1c-f920-4724-a761-d787d49d9b48

import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.Sub.Unbundled.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/--
The survival condition over an absolute interval is equivalent to the
same condition over elapsed time after the observation time.
-/
theorem solution
    (f : ℝ≥0 → ℝ) (x : ℝ) (s u : ℝ≥0) :
    (∀ v : ℝ≥0, s ≤ v → v ≤ s + u →
      0 ≤ (x + f s) + (f v - f s)) ↔
    (∀ v : ℝ≥0, v ≤ u →
      0 ≤ (x + f s) + (f (s + v) - f s)) := by
  constructor
  · intro h v hv
    exact h (s + v) (le_add_of_nonneg_right (show 0 ≤ v from zero_le))
      (add_le_add_right hv s)
  · intro h v hsv hv
    have hEq : s + (v - s) = v := add_tsub_cancel_of_le hsv
    have hw : v - s ≤ u := by
      have hSub := tsub_le_tsub_right hv s
      simpa only [add_tsub_cancel_left] using hSub
    simpa only [hEq] using h (v - s) hw
