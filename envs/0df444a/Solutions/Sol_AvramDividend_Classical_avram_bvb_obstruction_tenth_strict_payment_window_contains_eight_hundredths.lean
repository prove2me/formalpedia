-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_tenth_strict_payment_window_contains_eight_hundredths
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:03:11.304134+00:00
-- url     : https://prove2.me/submissions/579e8d70-1640-4e41-a46a-575dc71adb05

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_tenth_horizon_strict_prefix_contains_eight_hundredths
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    (σ : ℝ≥0∞)
    (hσ : ((1 / 10 : ℝ≥0) : ℝ≥0∞) < σ)
    (n : ℕ) (hn : 4 ≤ n) :
    Ioc (0 : ℝ) (2 / 25 : ℝ) ⊆
      paymentTimes σ ∩
        Iio ((1 / 10 : ℝ) - (1 / 10 : ℝ) / ((n : ℝ) + 2)) := by
  intro t ht
  have ht0 : 0 < t := ht.1
  have ht8 : t ≤ (2 / 25 : ℝ) := ht.2
  have hBound :=
    avram_bvb_obstruction_tenth_horizon_strict_prefix_contains_eight_hundredths
      n hn
  have hSmall : ENNReal.ofReal t <
      ((1 / 10 : ℝ≥0) : ℝ≥0∞) := by
    have h0 : ENNReal.ofReal t ≤ ENNReal.ofReal (2 / 25 : ℝ) :=
      ENNReal.ofReal_le_ofReal ht8
    have h8 : ENNReal.ofReal (2 / 25 : ℝ) <
        ((1 / 10 : ℝ≥0) : ℝ≥0∞) := by
          apply (ENNReal.ofReal_lt_coe_iff (by norm_num : 0 ≤ (2 / 25 : ℝ))).2
          norm_num
    exact lt_of_le_of_lt h0 h8
  constructor
  · change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ)
    exact ⟨le_of_lt ht0, Or.inr (lt_trans hSmall hσ)⟩
  · exact lt_of_le_of_lt ht8 hBound
