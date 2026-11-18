-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB161_original_strict_prepayment_times_are_nonnegative_horizon_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:26:01.24521+00:00
-- url     : https://prove2.me/submissions/67f5c8f1-ce1c-4ac5-a979-607c539a33bf

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Original strict payment support lies in the nonnegative stopped horizon. -/
theorem solution
    (σ : ℝ≥0∞) (T : ℝ≥0) :
    paymentTimes σ ∩ Iio (T : ℝ) ⊆
      Icc (0 : ℝ) (T : ℝ) := by
  intro t ht
  rcases ht with ⟨hPaid, hBefore⟩
  change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ) at hPaid
  exact ⟨hPaid.1, le_of_lt hBefore⟩
