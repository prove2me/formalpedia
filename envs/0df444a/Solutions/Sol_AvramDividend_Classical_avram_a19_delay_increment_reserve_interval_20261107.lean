-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_delay_increment_reserve_interval_20261107
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:41:41.641628+00:00
-- url     : https://prove2.me/submissions/c1d7e7d5-dbec-4a57-abbd-a64b5e064b6e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The small payment delay and increment preserve a positive reserve interval. -/
theorem solution
    (eps delta xi : ℝ)
    (heps : 0 < eps) (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ eps / 128)
    (hxi0 : 0 ≤ xi) (hxi : xi ≤ eps / 4) :
    (3 / 4 : ℝ) * eps ≤ eps + 2 * delta - xi ∧
      eps + 2 * delta - xi ≤ (65 / 64 : ℝ) * eps := by
  constructor <;> linarith
