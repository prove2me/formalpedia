-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_min_zero_eq_singleton_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T13:59:57.33317+00:00
-- url     : https://prove2.me/submissions/4027843c-a116-451c-82fa-82c078bccbfe

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A zero truncation retains exactly the payment at time zero,
    independently of whether ruin also occurs at time zero. -/
theorem solution (σ : ℝ≥0∞) :
    paymentTimes (min σ (0 : ℝ≥0∞)) = ({0} : Set ℝ) := by
  ext t
  constructor
  · intro ht
    rcases ht.2 with hzero | hpre
    · exact Set.mem_singleton_iff.mpr hzero
    · have hneg : ENNReal.ofReal t < (0 : ℝ≥0∞) :=
        lt_of_lt_of_le hpre (min_le_right _ _)
      exact False.elim ((not_lt_of_ge (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal t)) hneg)
  · intro ht
    have hzero : t = 0 := Set.mem_singleton_iff.mp ht
    exact ⟨by simp [hzero], Or.inl hzero⟩
