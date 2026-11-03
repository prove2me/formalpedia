-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_positive_horizon_endpoint_not_in_min_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:55:08.709348+00:00
-- url     : https://prove2.me/submissions/a6d8d702-50bd-4d28-b460-1d75a839396e

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A positive real observation horizon is excluded by a clock truncated
    exactly there: any terminal Stieltjes dividend atom must be restored. -/
theorem solution
    (σ : ℝ≥0∞) (T : ℝ) (hT : 0 < T) :
    T ∉ paymentTimes (min σ (ENNReal.ofReal T)) := by
  intro ht
  rcases ht.2 with hz | hlt
  · exact (ne_of_gt hT) hz
  · exact (not_lt_of_ge (min_le_right σ (ENNReal.ofReal T))) hlt
