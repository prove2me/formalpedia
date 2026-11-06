-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_real_stopped_paymentTimes_closed_window_saturation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:14:18.708193+00:00
-- url     : https://prove2.me/submissions/7e448ba2-3c54-4c38-98b5-db0878adac5a

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_real_stopped_paymentTimes_subset_closed_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (τ : ℝ≥0∞) (S T : ℝ) (hS : 0 ≤ S) (hST : S ≤ T) :
    paymentTimes (min τ (ENNReal.ofReal S)) ∩ Set.Iic T =
    paymentTimes (min τ (ENNReal.ofReal S)) ∩ Set.Iic S := by
  ext t
  constructor
  · rintro ⟨ht, _⟩
    exact ⟨ht, avram_limit2_real_stopped_paymentTimes_subset_closed_horizon τ S hS ht⟩
  · rintro ⟨ht, hts⟩
    refine ⟨ht, ?_⟩
    change t ≤ T
    have hs : t ≤ S := by simpa only [Set.mem_Iic] using hts
    exact hs.trans hST
