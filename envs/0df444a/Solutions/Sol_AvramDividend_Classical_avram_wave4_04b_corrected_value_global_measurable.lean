-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_corrected_value_global_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:28:25.139995+00:00
-- url     : https://prove2.me/submissions/51dc4edd-a9b5-4c2d-ac91-9985adeeeaf7

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped Classical
noncomputable section

/-- Continuity on the nonnegative side and zero extension below zero make w Borel. -/
theorem solution
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) :
    Measurable w := by
  classical
  have hp : Measurable ((Ici (0 : ℝ)).piecewise w (fun _ => (0 : ℝ))) :=
    hw_cont.measurable_piecewise
      (continuous_const.continuousOn) measurableSet_Ici
  convert hp using 1
  funext y
  by_cases hy : 0 ≤ y
  · simp [Set.piecewise, hy]
  · have hyneg : y < 0 := lt_of_not_ge hy
    simp [Set.piecewise, hy, hw_neg y hyneg]
