-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB152_original_strict_prepayment_cash_contains_short_physical_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:13:19.213686+00:00
-- url     : https://prove2.me/submissions/69f8ee7d-4b1c-45a8-a682-d648777ea02b

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Original strict pre-ruin payment set contains a short physical cash cell. -/
theorem solution
    (σ : ℝ≥0∞) (S T : ℝ≥0)
    (hS : (S : ℝ≥0∞) < σ)
    (hST : S < T) :
    Ioc (0 : ℝ) (S : ℝ) ⊆
      paymentTimes σ ∩ Iio (T : ℝ) := by
  intro z hz
  have hzOf : ENNReal.ofReal z ≤ (S : ℝ≥0∞) := by
    calc
      ENNReal.ofReal z ≤ ENNReal.ofReal (S : ℝ) :=
        ENNReal.ofReal_le_ofReal hz.2
      _ = (S : ℝ≥0∞) := by simp
  have hSTReal : (S : ℝ) < (T : ℝ) := hST
  constructor
  · change 0 ≤ z ∧ (z = 0 ∨ ENNReal.ofReal z < σ)
    exact ⟨hz.1.le, Or.inr (lt_of_le_of_lt hzOf hS)⟩
  · exact lt_of_le_of_lt hz.2 hSTReal
