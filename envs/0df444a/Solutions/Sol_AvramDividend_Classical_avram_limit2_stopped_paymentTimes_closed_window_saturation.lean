-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_stopped_paymentTimes_closed_window_saturation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:05:26.114669+00:00
-- url     : https://prove2.me/submissions/50a42426-a302-434a-9f8d-562d10f589d6

import Mathlib
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_limit2_stopped_paymentTimes_subset_closed_nat_clock

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (τ : ℝ≥0∞) (n : ℕ) (T : ℝ) (hT : (n : ℝ) ≤ T) :
    paymentTimes (min τ (n : ℝ≥0∞)) ∩ Set.Iic T =
    paymentTimes (min τ (n : ℝ≥0∞)) ∩ Set.Iic (n : ℝ) := by
  ext t
  constructor
  · rintro ⟨ht, _⟩
    exact ⟨ht, avram_limit2_stopped_paymentTimes_subset_closed_nat_clock τ n ht⟩
  · rintro ⟨ht, hn⟩
    exact ⟨ht, hn.trans hT⟩
