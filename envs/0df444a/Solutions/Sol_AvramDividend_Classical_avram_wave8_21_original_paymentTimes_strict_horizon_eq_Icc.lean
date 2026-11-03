-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_21_original_paymentTimes_strict_horizon_eq_Icc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:48:47.108999+00:00
-- url     : https://prove2.me/submissions/304d5ee0-de52-4fd8-8356-8297744f33b6

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Strict survival makes the actual original payment clock the full closed horizon. -/
theorem solution
    (σ : ℝ≥0∞) (T : ℝ≥0)
    (hstrict : (T : ℝ≥0∞) < σ) :
    paymentTimes σ ∩ Iic (T : ℝ) = Icc 0 (T : ℝ) := by
  ext t
  change ((0 ≤ t ∧
    (t = 0 ∨ ENNReal.ofReal t < σ)) ∧ t ≤ (T : ℝ)) ↔
      (0 ≤ t ∧ t ≤ (T : ℝ))
  constructor
  · intro ht
    exact ⟨ht.1.1, ht.2⟩
  · intro ht
    have hle : ENNReal.ofReal t ≤ (T : ℝ≥0∞) := by
      calc
        ENNReal.ofReal t ≤ ENNReal.ofReal (T : ℝ) :=
          ENNReal.ofReal_le_ofReal ht.2
        _ = (T : ℝ≥0∞) := by simp
    exact ⟨⟨ht.1, Or.inr (lt_of_le_of_lt hle hstrict)⟩, ht.2⟩
