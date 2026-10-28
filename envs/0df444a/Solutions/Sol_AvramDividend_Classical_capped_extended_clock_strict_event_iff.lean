-- Prove2me | solution 1 for AvramDividend.Classical.capped_extended_clock_strict_event_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:48:39.96933+00:00
-- url     : https://prove2.me/submissions/491b3397-8a1a-4df2-bb8e-245fef74a2d5

import Mathlib.Data.ENNReal.Real
import Mathlib.Data.NNReal.Basic
import Mathlib.Order.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

/-- Below a finite cap, strict survival of the capped real clock exactly
matches strict survival of the original extended clock. -/
theorem solution (τ : ℝ≥0∞) (T t : ℝ≥0) (ht : t < T) :
    (t : ℝ) < (min τ (T : ℝ≥0∞)).toReal ↔
      (t : ℝ≥0∞) < τ := by
  have hc : min τ (T : ℝ≥0∞) ≠ ∞ := by
    exact ne_top_of_le_ne_top (by simp)
      (min_le_right τ (T : ℝ≥0∞))
  have hiff : (t : ℝ) < (min τ (T : ℝ≥0∞)).toReal ↔
      (t : ℝ≥0∞) < min τ (T : ℝ≥0∞) := by
    simpa using
      (ENNReal.toReal_lt_toReal (a := (t : ℝ≥0∞))
        (b := min τ (T : ℝ≥0∞)) (by simp) hc)
  rw [hiff, lt_min_iff]
  exact and_iff_left (ENNReal.coe_lt_coe.mpr ht)
