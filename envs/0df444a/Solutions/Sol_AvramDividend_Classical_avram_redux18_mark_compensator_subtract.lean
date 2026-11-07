-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_mark_compensator_subtract
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:12:18.339705+00:00
-- url     : https://prove2.me/submissions/5241aa5d-9f50-4584-932c-7ddba88211f9

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-! Decompose the finite mark-band exponent into count mass and mark moment. -/
theorem solution
    (ν : Measure ℝ) (B : Set ℝ)
    (hOne : IntegrableOn (fun _ : ℝ => (1 : ℝ)) B ν)
    (hExp : IntegrableOn Real.exp B ν) :
    (∫ y in B, (1 - Real.exp y) ∂ν) =
      (ν B).toReal - (∫ y in B, Real.exp y ∂ν) := by
  rw [integral_sub hOne hExp]
  simp [Measure.real]