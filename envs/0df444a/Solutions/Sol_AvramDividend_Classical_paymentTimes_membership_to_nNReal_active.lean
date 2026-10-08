-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_membership_to_nNReal_active
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:17:57.264024+00:00
-- url     : https://prove2.me/submissions/4f314f6a-9f39-40c6-b60d-53f374b906ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (σ : ℝ≥0∞) (s : ℝ) (hs : s ∈ paymentTimes σ) :
    0 ≤ s ∧
      (s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < σ) := by
  change 0 ≤ s ∧ (s = 0 ∨ ENNReal.ofReal s < σ) at hs
  rcases hs with ⟨hs0, hpay⟩
  refine ⟨hs0, ?_⟩
  rcases hpay with h0 | hbefore
  · left
    subst s
    exact Real.toNNReal_zero
  · right
    simpa only [ENNReal.ofNNReal_toNNReal] using hbefore
