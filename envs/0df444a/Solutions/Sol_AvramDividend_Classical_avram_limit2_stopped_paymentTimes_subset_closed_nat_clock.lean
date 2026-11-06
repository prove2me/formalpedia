-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_stopped_paymentTimes_subset_closed_nat_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:57:35.863569+00:00
-- url     : https://prove2.me/submissions/e6b7b291-d23f-449e-be39-3c017d366872

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (τ : ℝ≥0∞) (n : ℕ) :
    paymentTimes (min τ (n : ℝ≥0∞)) ⊆ Set.Iic (n : ℝ) := by
  intro t ht
  change (0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < min τ (n : ℝ≥0∞))) at ht
  rcases ht with ⟨ht0, hzero | hlt⟩
  · subst t
    change (0 : ℝ) ≤ (n : ℝ)
    exact_mod_cast Nat.zero_le n
  · have hlt_n : ENNReal.ofReal t < (n : ℝ≥0∞) :=
      lt_of_lt_of_le hlt (min_le_right τ (n : ℝ≥0∞))
    by_contra hn
    have htn : (n : ℝ) ≤ t := le_of_lt (lt_of_not_ge hn)
    have hmono : (n : ℝ≥0∞) ≤ ENNReal.ofReal t := by
      simpa using (ENNReal.ofReal_mono htn)
    exact (not_le_of_gt hlt_n) hmono
