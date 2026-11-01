-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_measurable_interior_deriv_zero_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:33:28.574826+00:00
-- url     : https://prove2.me/submissions/d7ca1283-8466-4a5b-a9f5-c07fb5010872

import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped Classical
noncomputable section
theorem solution
    (w : ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (hw : ContDiffOn ℝ 2 w s) :
    Measurable (fun y : ℝ => if y ∈ s then deriv w y else 0) := by
  classical
  have hder : ContinuousOn (deriv w) s :=
    hw.continuousOn_deriv_of_isOpen hs (by norm_num)
  change Measurable (s.piecewise (deriv w) (fun _ => (0 : ℝ)))
  exact hder.measurable_piecewise continuous_const.continuousOn hs.measurableSet
