-- Prove2me | solution 1 for AvramDividend.Classical.positive_jump_tail_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:07:07.12533+00:00
-- url     : https://prove2.me/submissions/aa9a3b57-cb31-4af5-be7b-601b63d37e89

import Mathlib.MeasureTheory.Integral.Layercake

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- All strict jump-magnitude tail masses decrease with the threshold. -/
theorem solution (μ : Measure ℝ≥0) :
    Antitone (fun t : ℝ => μ {z : ℝ≥0 | t < (z : ℝ)}) := by
  intro x y hxy
  apply measure_mono
  intro z hz
  exact lt_of_le_of_lt hxy hz
