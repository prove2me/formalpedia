-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_value_measurable_of_positive_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:14:00.451126+00:00
-- url     : https://prove2.me/submissions/48059850-4096-4158-9536-f895c3e99b85

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical
noncomputable section

/-- The original BV barrier value is measurable with its permitted zero-origin jump: continuity on nonnegative reserves and zero values below zero suffice. -/
theorem solution (w : ℝ → ℝ)
  (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
  (hw_neg : ∀ y : ℝ, y < 0 → w y = 0) :
  Measurable w := by
  classical
  have hPiece : Measurable ((Ici (0 : ℝ)).piecewise w (fun _ => (0 : ℝ))) :=
    hw_cont.measurable_piecewise continuous_const.continuousOn measurableSet_Ici
  have hEq : (Ici (0 : ℝ)).piecewise w (fun _ => (0 : ℝ)) = w := by
    funext y
    by_cases hy : 0 ≤ y
    · simp [Set.piecewise, hy]
    · have hlt : y < 0 := lt_of_not_ge hy
      simp [Set.piecewise, hy, hw_neg y hlt]
  rw [← hEq]
  exact hPiece