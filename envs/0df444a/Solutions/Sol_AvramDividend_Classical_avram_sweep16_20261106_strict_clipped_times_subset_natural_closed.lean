-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_20261106_strict_clipped_times_subset_natural_closed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:36:41.930703+00:00
-- url     : https://prove2.me/submissions/b88b97e5-c7a1-4d80-be22-c47158e5f316

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    (σ : ℝ≥0∞) (n : ℕ) :
    paymentTimes (min σ (n : ℝ≥0∞)) ⊆
      paymentTimes σ ∩ Set.Iic (((min σ (n : ℝ≥0∞)).toNNReal : ℝ)) := by
  intro t ht
  change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < min σ (n : ℝ≥0∞)) at ht
  rcases ht with ⟨ht0, htime⟩
  have hfinite : min σ (n : ℝ≥0∞) ≠ ⊤ := by simp
  constructor
  · change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ)
    exact ⟨ht0, htime.elim Or.inl (fun h => Or.inr (lt_of_lt_of_le h (min_le_left _ _)))⟩
  · change t ≤ (min σ (n : ℝ≥0∞)).toReal
    rcases htime with hzero | hpositive
    · subst t
      exact ENNReal.toReal_nonneg
    · exact le_of_lt ((ENNReal.ofReal_lt_iff_lt_toReal ht0 hfinite).mp hpositive)
