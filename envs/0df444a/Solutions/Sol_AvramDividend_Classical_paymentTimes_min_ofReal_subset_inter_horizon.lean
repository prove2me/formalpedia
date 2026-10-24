-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_min_ofReal_subset_inter_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:35:03.631866+00:00
-- url     : https://prove2.me/submissions/49a4cde8-f537-4115-b0e6-499608a8002c

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Truncating the ruin clock at a real horizon preserves every selected
    payment time's ruin condition and bounds its real time by the horizon.
    The atom at time zero is retained even when the horizon is zero. -/
theorem solution (σ : ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T) :
    paymentTimes (min σ (ENNReal.ofReal T)) ⊆
      paymentTimes σ ∩ Set.Iic T := by
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  rcases ht.2 with hzero | hpre
  · have htσ : t ∈ paymentTimes σ := ⟨ht0, Or.inl hzero⟩
    have htt : t ≤ T := by
      rw [hzero]
      exact hT
    exact ⟨htσ, htt⟩
  · have htσ : t ∈ paymentTimes σ :=
      ⟨ht0, Or.inr (lt_of_lt_of_le hpre (min_le_left _ _))⟩
    have htT : ENNReal.ofReal t < ENNReal.ofReal T :=
      lt_of_lt_of_le hpre (min_le_right _ _)
    have htt : t ≤ T := by
      by_contra hn
      have hgt : T < t := lt_of_not_ge hn
      have hmono : ENNReal.ofReal T ≤ ENNReal.ofReal t :=
        ENNReal.ofReal_le_ofReal (le_of_lt hgt)
      exact (not_le_of_gt htT) hmono
    exact ⟨htσ, htt⟩
