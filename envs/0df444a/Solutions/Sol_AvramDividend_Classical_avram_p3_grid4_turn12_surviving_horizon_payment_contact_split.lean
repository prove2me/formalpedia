-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_turn12_surviving_horizon_payment_contact_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:50:25.908363+00:00
-- url     : https://prove2.me/submissions/5a0c3fe9-72e8-449c-a427-2412c8679b1c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- At a surviving horizon the only excess contact mass is its endpoint. -/
theorem solution
    (σ : ℝ≥0∞) (a b : ℝ) (hb : 0 ≤ b)
    (hpre : ENNReal.ofReal b < σ) (hab : a < b) :
    paymentTimes σ ∩ Ioc a b =
      (paymentTimes σ ∩ Ioo a b) ∪ {b} := by
  ext t
  constructor
  · rintro ⟨htPay, ⟨hat, htb⟩⟩
    rcases lt_or_eq_of_le htb with hlt | heq
    · exact Or.inl ⟨htPay, ⟨hat, hlt⟩⟩
    · exact Or.inr heq
  · rintro (⟨htPay, ⟨hat, htb⟩⟩ | heq)
    · exact ⟨htPay, ⟨hat, htb.le⟩⟩
    · subst t
      exact ⟨⟨hb, Or.inr hpre⟩, ⟨hab, le_refl b⟩⟩
