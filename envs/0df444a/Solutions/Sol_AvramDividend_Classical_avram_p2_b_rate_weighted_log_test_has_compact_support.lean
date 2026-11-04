-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_has_compact_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:18:12.653414+00:00
-- url     : https://prove2.me/submissions/58c9ea5b-d656-4ef8-83c5-787bbf4a53ff

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution
    (f : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0) :
    HasCompactSupport (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Icc (-Real.exp (-ε)) (Real.exp (-ε))) isCompact_Icc
  intro z hz
  have hz_ne : f (Real.log z) / (z - 1) ^ 4 ≠ 0 := hz
  have habs : |z| ≤ Real.exp (-ε) := by
    by_contra hn
    have hgt : Real.exp (-ε) < |z| := lt_of_not_ge hn
    have hpos : 0 < |z| := (Real.exp_pos (-ε)).trans hgt
    have hlogabs : -ε < Real.log |z| :=
      (Real.lt_log_iff_exp_lt hpos).mpr hgt
    have hlog : -ε < Real.log z := by
      simpa only [Real.log_abs] using hlogabs
    have hzero : f (Real.log z) = 0 :=
      hfupper (Real.log z) hlog
    exact hz_ne (by simp [hzero])
  exact (abs_le.mp habs)
