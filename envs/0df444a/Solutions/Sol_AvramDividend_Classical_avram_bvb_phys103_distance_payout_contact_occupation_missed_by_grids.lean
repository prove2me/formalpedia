-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys103_distance_payout_contact_occupation_missed_by_grids
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:53:55.676173+00:00
-- url     : https://prove2.me/submissions/d21ac0bf-a921-4330-9fde-a11ce3f9092f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys101_positive_contact_set_strictly_missed_by_grids
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys98_distance_contact_dividend_monotone_zero_initial

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A continuous monotone payout schedule creates positive-volume reserve
contact that is strictly absent at every deterministic physical-grid time. -/
theorem solution (u : ℕ → ℕ → ℝ) :
    ∃ K : Set ℝ, 0 < (volume : Measure ℝ) K ∧
      Monotone (fun t : ℝ =>
        t + Metric.infDist t K - Metric.infDist 0 K) ∧
      ((0 : ℝ) + Metric.infDist 0 K - Metric.infDist 0 K) = 0 ∧
      (∀ t ∈ K, t - (t + Metric.infDist t K - Metric.infDist 0 K) =
        Metric.infDist 0 K) ∧
      (∀ n i : ℕ, u n i -
        (u n i + Metric.infDist (u n i) K - Metric.infDist 0 K) <
          Metric.infDist 0 K) := by
  obtain ⟨K, _, _, hpos, hgrid⟩ :=
    AvramDividend.Classical.avram_bvb_phys101_positive_contact_set_strictly_missed_by_grids u
  obtain ⟨hmono, hzero⟩ :=
    AvramDividend.Classical.avram_bvb_phys98_distance_contact_dividend_monotone_zero_initial K
  refine ⟨K, hpos, hmono, hzero, ?_, ?_⟩
  · intro t ht
    have hz : Metric.infDist t K = 0 := Metric.infDist_zero_of_mem ht
    rw [hz]
    ring
  · intro n i
    have hp := hgrid n i
    linarith
