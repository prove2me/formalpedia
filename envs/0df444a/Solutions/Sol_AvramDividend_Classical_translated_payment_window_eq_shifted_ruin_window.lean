-- Prove2me | solution 1 for AvramDividend.Classical.translated_payment_window_eq_shifted_ruin_window
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:27:59.811408+00:00
-- url     : https://prove2.me/submissions/534af44f-a220-40c3-be4e-6b39b70a5325

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_translated_iff_shifted_of_pos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (u : ℝ≥0) (ρ : ℝ≥0∞) :
    Set.Ioi (0 : ℝ) ∩
      ((fun t : ℝ => (u : ℝ) + t) ⁻¹'
        paymentTimes ((u : ℝ≥0∞) + ρ)) =
    Set.Ioi (0 : ℝ) ∩ paymentTimes ρ := by
  ext t
  simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_preimage]
  constructor
  · rintro ⟨ht, hmem⟩
    exact ⟨ht, (paymentTimes_translated_iff_shifted_of_pos
      u ρ t ht).mp hmem⟩
  · rintro ⟨ht, hmem⟩
    exact ⟨ht, (paymentTimes_translated_iff_shifted_of_pos
      u ρ t ht).mpr hmem⟩
