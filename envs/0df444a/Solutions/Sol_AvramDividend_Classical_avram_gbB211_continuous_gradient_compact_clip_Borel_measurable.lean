-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB211_continuous_gradient_compact_clip_Borel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:42:11.511208+00:00
-- url     : https://prove2.me/submissions/2ddce4eb-9eab-423d-9f63-2a3639bd05f4

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
noncomputable section

/-- A compact-interval continuous gradient gives a measurable piecewise clip. -/
theorem solution
    (w : ℝ → ℝ) (a b : ℝ)
    (hContinuous : ContinuousOn (deriv w) (Icc a b)) :
    Measurable (fun y : ℝ =>
      if y ∈ Icc a b then deriv w y else 1) := by
  classical
  exact hContinuous.measurable_piecewise continuousOn_const
    isClosed_Icc.measurableSet

