-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_eq_strict_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T21:17:24.5225+00:00
-- url     : https://prove2.me/submissions/8ac6c847-e7df-4542-947a-561b1bdcd259

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (τ : ℝ≥0∞) (hτ : 0 < τ) :
    paymentTimes τ = {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < τ} := by
  ext t
  change (0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < τ)) ↔
    (0 ≤ t ∧ ENNReal.ofReal t < τ)
  constructor
  · rintro ⟨h0, hpay⟩
    refine ⟨h0, ?_⟩
    rcases hpay with hz | hlt
    · subst t
      simpa using hτ
    · exact hlt
  · rintro ⟨h0, hlt⟩
    exact ⟨h0, Or.inr hlt⟩
