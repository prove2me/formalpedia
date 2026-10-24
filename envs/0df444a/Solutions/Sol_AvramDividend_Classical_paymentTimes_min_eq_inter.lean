-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_min_eq_inter
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:03:15.481749+00:00
-- url     : https://prove2.me/submissions/f0597dc5-946f-48ff-99cb-8f064f0044c3

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Payment times for the minimum of two stopping clocks are exactly their
    intersection; the special initial payment atom survives both clocks. -/
theorem solution (σ τ : ℝ≥0∞) :
    paymentTimes (min σ τ) = paymentTimes σ ∩ paymentTimes τ := by
  ext t
  constructor
  · intro ht
    rcases ht.2 with hzero | hpre
    · exact ⟨⟨ht.1, Or.inl hzero⟩, ⟨ht.1, Or.inl hzero⟩⟩
    · exact ⟨⟨ht.1, Or.inr (lt_of_lt_of_le hpre (min_le_left _ _))⟩,
        ⟨ht.1, Or.inr (lt_of_lt_of_le hpre (min_le_right _ _))⟩⟩
  · rintro ⟨⟨ht0, hzero | hσ⟩, ⟨_, hzeroτ | hτ⟩⟩
    · exact ⟨ht0, Or.inl hzero⟩
    · exact ⟨ht0, Or.inl hzero⟩
    · exact ⟨ht0, Or.inl hzeroτ⟩
    · exact ⟨ht0, Or.inr (lt_min hσ hτ)⟩
