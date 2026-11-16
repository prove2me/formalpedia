-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a544_positive_C0_value_Borel_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:57:16.05212+00:00
-- url     : https://prove2.me/submissions/371fb34c-e70d-4731-8f12-76028c82c5ef

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw : ContinuousOn w (Set.Ioi (0 : ℝ))) :
    Measurable (fun y : ℝ => if 0 < y then w y else w 0) := by
  classical
  have h := ContinuousOn.measurable_piecewise
    (s := Set.Ioi (0 : ℝ)) (g := fun _ : ℝ => w 0)
    hw (continuousOn_const) measurableSet_Ioi
  convert h using 1
  funext y
  by_cases hy : 0 < y
  · simp [Set.piecewise, hy]
  · simp [Set.piecewise, hy]
