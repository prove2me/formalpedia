-- Prove2me | solution 1 for AvramDividend.Classical.chat04_closed_survival_iff_negative_times_after_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:26:18.834061+00:00
-- url     : https://prove2.me/submissions/14760ab5-dbb7-4464-a2a8-effd089118a6

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- Closed-horizon survival precisely excludes negative reserves at or before the horizon. -/
theorem solution
    (f : NNReal → ℝ) (t : NNReal) :
    (∀ s : NNReal, s ≤ t → 0 ≤ f s) ↔
      ∀ s : NNReal, f s < 0 → t < s := by
  constructor
  · intro hsurv s hneg
    by_contra hnot
    have hst : s ≤ t := le_of_not_gt hnot
    exact (not_lt_of_ge (hsurv s hst)) hneg
  · intro hafter s hst
    by_contra hnot
    have hneg : f s < 0 := lt_of_not_ge hnot
    exact (not_lt_of_ge hst) (hafter s hneg)
