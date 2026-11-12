-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys98_distance_contact_dividend_monotone_zero_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:32:18.662511+00:00
-- url     : https://prove2.me/submissions/88a5097c-3f31-4b6a-810c-83327eafb13d

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- The distance-profile contact construction gives a nondecreasing
deterministic dividend path, with zero initial payout. -/
theorem solution (F : Set ℝ) :
    Monotone (fun t : ℝ => t + Metric.infDist t F - Metric.infDist 0 F) ∧
      ((0 : ℝ) + Metric.infDist 0 F - Metric.infDist 0 F) = 0 := by
  constructor
  · intro s t hst
    have h := Metric.infDist_le_infDist_add_dist (s := F) (x := s) (y := t)
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)] at h
    dsimp
    linarith
  · simp
