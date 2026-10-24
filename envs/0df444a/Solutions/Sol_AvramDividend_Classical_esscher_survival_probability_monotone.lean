-- Prove2me | solution 1 for AvramDividend.Classical.esscher_survival_probability_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:44:19.958227+00:00
-- url     : https://prove2.me/submissions/71458c14-83ec-4a36-b200-d4365bdcf478

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal

/-!
The set of paths that never go below zero is monotone in the
initial reserve. Measure monotonicity then gives the survival bound.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ) (x y : ℝ) (hxy : x ≤ y) :
    P {ω | ∀ t : ℝ≥0, 0 ≤ x + Z t ω} ≤
      P {ω | ∀ t : ℝ≥0, 0 ≤ y + Z t ω} := by
  apply measure_mono
  intro ω hω
  change ∀ t : ℝ≥0, 0 ≤ y + Z t ω
  intro t
  have ht := hω t
  linarith
