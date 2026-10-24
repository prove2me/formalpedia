-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_min_ofReal_eq_inter_Iio_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:56:26.308272+00:00
-- url     : https://prove2.me/submissions/ff40eb0e-3211-42dc-94ff-29374906a3fc

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- For a strictly positive deterministic horizon, truncating the ruin
    clock selects precisely the payment times strictly before the horizon.
    The initial atom is included, even when ruin occurs at time zero. -/
theorem solution (σ : ℝ≥0∞) (T : ℝ) (hT : 0 < T) :
    paymentTimes (min σ (ENNReal.ofReal T)) =
      paymentTimes σ ∩ Set.Iio T := by
  ext t
  constructor
  · intro ht
    have ht0 : 0 ≤ t := ht.1
    rcases ht.2 with hzero | hpre
    · exact ⟨⟨ht0, Or.inl hzero⟩, by simpa [hzero] using hT⟩
    · have htσ : ENNReal.ofReal t < σ :=
        lt_of_lt_of_le hpre (min_le_left _ _)
      have htT : ENNReal.ofReal t < ENNReal.ofReal T :=
        lt_of_lt_of_le hpre (min_le_right _ _)
      exact ⟨⟨ht0, Or.inr htσ⟩,
        (ENNReal.ofReal_lt_ofReal_iff hT).mp htT⟩
  · rintro ⟨⟨ht0, hzero | hσ⟩, htT⟩
    · exact ⟨ht0, Or.inl hzero⟩
    · have htReal : ENNReal.ofReal t < ENNReal.ofReal T :=
        (ENNReal.ofReal_lt_ofReal_iff hT).mpr htT
      exact ⟨ht0, Or.inr (lt_min hσ htReal)⟩
