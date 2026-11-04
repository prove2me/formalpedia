-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_payment_window_closed_horizon_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:32:50.571564+00:00
-- url     : https://prove2.me/submissions/1ab22680-ffea-4d32-8c32-870389c624be

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The literal original stopped-payment window has the closed zero endpoint. -/
theorem solution
    (σ : ℝ≥0∞) (T : ℝ≥0) :
    paymentTimes σ ∩ Iic (T : ℝ) =
      paymentTimes σ ∩ Icc (0 : ℝ) (T : ℝ) := by
  ext s
  constructor
  · rintro ⟨hPay, hT⟩
    exact ⟨hPay, ⟨(paymentTimes_membership_to_nNReal_active σ s hPay).1, hT⟩⟩
  · rintro ⟨hPay, h0, hT⟩
    exact ⟨hPay, hT⟩
