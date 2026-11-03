-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_positive_n_paymentTimes_le_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:52:24.874748+00:00
-- url     : https://prove2.me/submissions/a4fb57ad-9025-4ec8-8cee-2b545feba36c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    (σ : ℝ≥0∞) (n : ℕ) (hn : 0 < n) :
    paymentTimes (min σ (n : ℝ≥0∞)) ⊆ Iic (n : ℝ) := by
  intro t ht
  change t ≤ (n : ℝ)
  change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < min σ (n : ℝ≥0∞)) at ht
  rcases ht.2 with heq | hlt
  · subst t
    exact_mod_cast Nat.zero_le n
  · have hltN : ENNReal.ofReal t < (n : ℝ≥0∞) :=
      lt_of_lt_of_le hlt (min_le_right σ (n : ℝ≥0∞))
    have hltR : t < (n : ℝ) :=
      (ENNReal.ofReal_lt_natCast (Nat.ne_of_gt hn)).mp hltN
    exact le_of_lt hltR
