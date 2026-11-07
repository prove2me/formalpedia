-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_nonint_C1_deriv_zero_extension_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:56:45.020249+00:00
-- url     : https://prove2.me/submissions/43421be2-031b-482f-8512-766143a60841

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory
noncomputable section

theorem solution
    (w : ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (hw : ContDiffOn ℝ 1 w s) :
    Measurable (fun y : ℝ => if y ∈ s then deriv w y else 0) := by
  classical
  have hder : ContinuousOn (deriv w) s :=
    hw.continuousOn_deriv_of_isOpen hs (by norm_num)
  change Measurable (s.piecewise (deriv w) (fun _ => (0 : ℝ)))
  exact hder.measurable_piecewise continuous_const.continuousOn hs.measurableSet
