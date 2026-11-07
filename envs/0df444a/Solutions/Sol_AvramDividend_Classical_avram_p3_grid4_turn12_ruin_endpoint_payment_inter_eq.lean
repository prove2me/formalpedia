-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_turn12_ruin_endpoint_payment_inter_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:46:02.256035+00:00
-- url     : https://prove2.me/submissions/4e8e9e6e-1505-41b9-aa2e-05161ec1ed5d

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- A strictly positive ruin endpoint cannot carry a pre-ruin payment. -/
theorem solution
    (σ : ℝ≥0∞) (b : ℝ) (hb : 0 < b)
    (hσ : ENNReal.ofReal b = σ) (a : ℝ) :
    paymentTimes σ ∩ Ioc a b = paymentTimes σ ∩ Ioo a b := by
  ext t
  constructor
  · rintro ⟨htPay, ⟨hat, htb⟩⟩
    have hne : t ≠ b := by
      intro heq
      have hp : 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ) := htPay
      rcases hp.2 with hz | hlt
      · exact (ne_of_gt hb) (heq ▸ hz)
      · rw [heq, hσ] at hlt
        exact (lt_irrefl σ hlt)
    exact ⟨htPay, ⟨hat, lt_of_le_of_ne htb hne⟩⟩
  · rintro ⟨htPay, ⟨hat, htb⟩⟩
    exact ⟨htPay, ⟨hat, htb.le⟩⟩
