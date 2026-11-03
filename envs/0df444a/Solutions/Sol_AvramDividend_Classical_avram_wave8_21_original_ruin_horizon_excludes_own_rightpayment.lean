-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_21_original_ruin_horizon_excludes_own_rightpayment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:44:26.428813+00:00
-- url     : https://prove2.me/submissions/4ac14bf2-65dd-4091-9b9a-2d4b0b45df5c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- At an immediate positive ruin horizon, the original payment clock retains zero and excludes its terminal rightpayment. -/
theorem solution
    (T : ℝ≥0) (hT : 0 < T) :
    (0 : ℝ) ∈ paymentTimes (T : ℝ≥0∞) ∧
    ((T : ℝ) ∉ paymentTimes (T : ℝ≥0∞)) := by
  constructor
  · change 0 ≤ (0 : ℝ) ∧
      ((0 : ℝ) = 0 ∨ ENNReal.ofReal (0 : ℝ) < (T : ℝ≥0∞))
    exact ⟨le_refl _, Or.inl rfl⟩
  · intro hPay
    change 0 ≤ (T : ℝ) ∧
      ((T : ℝ) = 0 ∨ ENNReal.ofReal (T : ℝ) < (T : ℝ≥0∞)) at hPay
    rcases hPay.2 with hZero | hStrict
    · have hPositive : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
      exact (ne_of_gt hPositive) hZero
    · have hEq : ENNReal.ofReal (T : ℝ) = (T : ℝ≥0∞) := by simp
      rw [hEq] at hStrict
      exact (lt_irrefl _) hStrict
