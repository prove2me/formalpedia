-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_Ioc_subset_of_terminal_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:42:14.20499+00:00
-- url     : https://prove2.me/submissions/23f1cd4b-aa99-4456-8481-76f679792a64

import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    (τ : ℝ≥0∞) (s t : ℝ) (hs : 0 ≤ s)
    (ht : ENNReal.ofReal t < τ) :
    Set.Ioc s t ⊆ paymentTimes τ := by
  have hτ : (0 : ℝ≥0∞) < τ := by
    exact lt_of_le_of_lt
      (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal t from zero_le) ht
  rw [paymentTimes_eq_strict_of_pos τ hτ]
  intro r hr
  exact ⟨le_trans hs (le_of_lt hr.1),
    lt_of_le_of_lt (ENNReal.ofReal_mono hr.2) ht⟩
