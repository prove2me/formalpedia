-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_positive_n_paymentTimes_source_ruin_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:03:31.837177+00:00
-- url     : https://prove2.me/submissions/e2146970-a53f-485b-9dbd-4584e287cb00

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_positive_n_paymentTimes_le_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    (σ : ℝ≥0∞) (n : ℕ) (hn : 0 < n) :
    paymentTimes (min σ (n : ℝ≥0∞)) ⊆
      paymentTimes σ ∩ Iic (n : ℝ) := by
  intro t ht
  refine ⟨?_, avram_wave7_08_positive_n_paymentTimes_le_clock σ n hn ht⟩
  change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ)
  change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < min σ (n : ℝ≥0∞)) at ht
  refine ⟨ht.1, ?_⟩
  rcases ht.2 with hzero | hlt
  · exact Or.inl hzero
  · exact Or.inr (lt_of_lt_of_le hlt (min_le_left σ (n : ℝ≥0∞)))
