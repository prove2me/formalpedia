-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_payment_times_supremum_clock_union
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:41:16.367095+00:00
-- url     : https://prove2.me/submissions/4ef5fba5-95a1-4a22-ab75-a0bf9bed413c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Supremum of chronological stopping clocks has precisely the union of
their right-payment eligibility sets, including the payment at time zero. -/
theorem solution (τ : ℕ → ℝ≥0∞) :
    paymentTimes (⨆ n, τ n) = ⋃ n, paymentTimes (τ n) := by
  ext s
  simp only [paymentTimes, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_Ici, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hs0, hs | hs⟩
    · exact ⟨0, hs0, Or.inl hs⟩
    · obtain ⟨n, hn⟩ := (lt_iSup_iff.mp hs)
      exact ⟨n, hs0, Or.inr hn⟩
  · rintro ⟨n, hs0, hs | hs⟩
    · exact ⟨hs0, Or.inl hs⟩
    · exact ⟨hs0, Or.inr (lt_of_lt_of_le hs (le_iSup τ n))⟩
