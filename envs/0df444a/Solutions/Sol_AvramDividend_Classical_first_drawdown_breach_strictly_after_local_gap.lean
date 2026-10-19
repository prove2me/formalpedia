-- Prove2me | solution 1 for AvramDividend.Classical.first_drawdown_breach_strictly_after_local_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T10:46:02.366008+00:00
-- url     : https://prove2.me/submissions/978cf23f-9e6e-4e38-b33e-e0fdfbd20ae8

import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.CompleteLattice.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

theorem solution
    (f : ℝ≥0 → ℝ) (a : ℝ)
    (u δ : ℝ≥0) (hδ : 0 < δ)
    (hNoBreach : ∀ t : ℝ≥0, t < u + δ → f t ≤ a) :
    (u : ℝ≥0∞) <
      (⨅ (t : ℝ≥0) (_ : a < f t), (t : ℝ≥0∞)) := by
  have hstrict : u < u + δ := by
    simpa using add_lt_add_left hδ u
  have hstrict' : (u : ℝ≥0∞) <
      ((u + δ : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_lt_coe.mpr hstrict
  have hbound : ((u + δ : ℝ≥0) : ℝ≥0∞) ≤
      (⨅ (t : ℝ≥0) (_ : a < f t), (t : ℝ≥0∞)) := by
    refine le_iInf fun t => le_iInf fun ht => ?_
    have htLower : u + δ ≤ t := by
      by_contra hn
      have hlt : t < u + δ := lt_of_not_ge hn
      exact (not_lt_of_ge (hNoBreach t hlt)) ht
    exact ENNReal.coe_le_coe.mpr htLower
  exact lt_of_lt_of_le hstrict' hbound
