-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_positive_horizon_endpoint_payment_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:08:46.829843+00:00
-- url     : https://prove2.me/submissions/3fdcbc01-c89e-45c9-9e30-37ffbe5fa153

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- For positive real T, an endpoint dividend is in the source payment set
    exactly when the genuine clock is strictly later than T. -/
theorem solution
    (σ : ℝ≥0∞) (T : ℝ) (hT : 0 < T) :
    T ∈ paymentTimes σ ↔ ENNReal.ofReal T < σ := by
  constructor
  · intro ht
    rcases ht.2 with hz | hlt
    · exact ((ne_of_gt hT) hz).elim
    · exact hlt
  · intro hlt
    exact ⟨le_of_lt hT, Or.inr hlt⟩
