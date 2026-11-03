-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_21_original_ruin_horizon_paymentTimes_eq_Ico
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:12:08.872387+00:00
-- url     : https://prove2.me/submissions/8a9f43c8-941f-42e3-a062-6605a8cace93

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- At strictly positive ruin time the original payment clock is exactly the half-open horizon. -/
theorem solution
    (T : ℝ≥0) (hT : 0 < T) :
    paymentTimes (T : ℝ≥0∞) ∩ Iic (T : ℝ) =
      Ico 0 (T : ℝ) := by
  ext t
  change ((0 ≤ t ∧
    (t = 0 ∨ ENNReal.ofReal t < (T : ℝ≥0∞))) ∧
      t ≤ (T : ℝ)) ↔ (0 ≤ t ∧ t < (T : ℝ))
  constructor
  · intro ht
    refine ⟨ht.1.1, ?_⟩
    rcases ht.1.2 with hzero | hstrict
    · rw [hzero]
      exact_mod_cast hT
    · by_contra hn
      have hge : (T : ℝ) ≤ t := le_of_not_gt hn
      have hgeENN : (T : ℝ≥0∞) ≤ ENNReal.ofReal t := by
        calc
          (T : ℝ≥0∞) = ENNReal.ofReal (T : ℝ) := by simp
          _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal hge
      exact (not_le_of_gt hstrict) hgeENN
  · intro ht
    have hpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
    have hltENN :
        ENNReal.ofReal t < ENNReal.ofReal (T : ℝ) :=
      (ENNReal.ofReal_lt_ofReal_iff hpos).2 ht.2
    have heq : ENNReal.ofReal (T : ℝ) = (T : ℝ≥0∞) := by simp
    exact ⟨⟨ht.1, Or.inr (by simpa only [heq] using hltENN)⟩,
      le_of_lt ht.2⟩
