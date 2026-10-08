-- Prove2me | solution 1 for AvramDividend.Classical.excursion_zero_cumulative_mass_implies_ae_support_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:21:17.401718+00:00
-- url     : https://prove2.me/submissions/8e20b1a6-9a5a-4611-b661-b959425a6273

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (β : Measure ℝ) (x : ℝ) (hzero : β (Iic x) = 0) :
    ∀ᵐ y : ℝ ∂β, x < y := by
  apply (ae_iff).2
  simpa only [not_lt, Set.Iic] using hzero
