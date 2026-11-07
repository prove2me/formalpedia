-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_zero_rate_mark_integrals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:19:02.647763+00:00
-- url     : https://prove2.me/submissions/29a3197c-06aa-4fac-9674-dbc3325a53bb

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.SpecialFunctions.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-! Mark moments and compensators on null Lévy bands vanish identically. -/
theorem solution
    (ν : Measure ℝ) (B : Set ℝ) (hZero : ν B = 0) :
    (∫ y in B, Real.exp y ∂ν) = 0 ∧
      (∫ y in B, (1 - Real.exp y) ∂ν) = 0 := by
  have hRestrict : ν.restrict B = 0 :=
    Measure.restrict_eq_zero.mpr hZero
  constructor <;> simp [hRestrict]