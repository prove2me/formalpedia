-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_strict_future_clock_preserves_finite_payment_set
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:45:18.202997+00:00
-- url     : https://prove2.me/submissions/7d81d2cb-2ffd-4086-a4f5-d5bd5a2496d3

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- If an auxiliary strict truncation clock exceeds the observation
    horizon, it preserves *all* original payments through the horizon,
    including a possible dividend at the right endpoint. -/
theorem solution
    (σ η : ℝ≥0∞) (T : ℝ)
    (hFuture : ENNReal.ofReal T < η) :
    paymentTimes σ ∩ Iic T =
      paymentTimes (min σ η) ∩ Iic T := by
  ext t
  constructor
  · rintro ⟨⟨ht0, hpay⟩, htT⟩
    refine ⟨⟨ht0, ?_⟩, htT⟩
    rcases hpay with hz | hlt
    · exact Or.inl hz
    · exact Or.inr (lt_min hlt
        (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal htT) hFuture))
  · rintro ⟨⟨ht0, hpay⟩, htT⟩
    refine ⟨⟨ht0, ?_⟩, htT⟩
    rcases hpay with hz | hlt
    · exact Or.inl hz
    · exact Or.inr (lt_of_lt_of_le hlt (min_le_left _ _))
