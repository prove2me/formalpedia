-- Prove2me | solution 1 for AvramDividend.Classical.chat03_integrable_of_integrable_real_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T10:07:58.095718+00:00
-- url     : https://prove2.me/submissions/7c597bdf-c629-472c-90a1-070bf2ea9afb

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-!
A real-valued strongly measurable L² function on a probability space
is integrable, via the pinned L² characterisation and finite measure.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZm : AEStronglyMeasurable Z P)
    (hZ2 : Integrable (fun ω => (Z ω) ^ 2) P) :
    Integrable Z P := by
  exact ((memLp_two_iff_integrable_sq hZm).mpr hZ2).integrable (by norm_num)
