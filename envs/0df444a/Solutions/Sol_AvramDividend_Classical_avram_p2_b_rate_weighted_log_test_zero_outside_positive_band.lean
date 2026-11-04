-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_zero_outside_positive_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:22:39.881746+00:00
-- url     : https://prove2.me/submissions/62811439-6278-4b04-a1ff-b36b49a06d26

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution
    (f : ℝ → ℝ) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0)
    (z : ℝ) (hz : 0 ≤ z)
    (hzout : z < Real.exp a ∨ Real.exp (-ε) < z) :
    f (Real.log z) / (z - 1) ^ 4 = 0 := by
  rcases hzout with hbelow | habove
  · rcases eq_or_lt_of_le hz with hzero | hpos
    · subst z
      have hfzero : f 0 = 0 := hfupper 0 (by linarith)
      simp [hfzero]
    · have hlog : Real.log z < a :=
        (Real.log_lt_iff_lt_exp hpos).mpr hbelow
      simp [hflower (Real.log z) hlog]
  · have hpos : 0 < z := (Real.exp_pos (-ε)).trans habove
    have hlog : -ε < Real.log z :=
      (Real.lt_log_iff_exp_lt hpos).mpr habove
    simp [hfupper (Real.log z) hlog]
