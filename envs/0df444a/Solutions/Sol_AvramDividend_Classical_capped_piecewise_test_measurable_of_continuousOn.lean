-- Prove2me | solution 1 for AvramDividend.Classical.capped_piecewise_test_measurable_of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:26:19.655882+00:00
-- url     : https://prove2.me/submissions/8171a3da-0102-49aa-8e4e-bd96369f4c3c

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A continuous finite-cap test extended by zero is Borel measurable. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ)
    (hw : ContinuousOn w (Icc (0 : ℝ) C)) :
    Measurable (fun y : ℝ => if y ∈ Icc (0 : ℝ) C then w y else 0) := by
  classical
  exact hw.measurable_piecewise continuousOn_const isClosed_Icc.measurableSet
