-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_positive_rate_mark_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:49:38.609198+00:00
-- url     : https://prove2.me/submissions/ff4385be-8ba2-494a-904c-feb1af27ca85

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_avram_redux18_mark_compensator_subtract
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-! Convert conditional Poisson mark moments to the Lévy compensator exponent. -/
theorem solution
    (ν : Measure ℝ) (B : Set ℝ)
    (hOne : IntegrableOn (fun _ : ℝ => (1 : ℝ)) B ν)
    (hExp : IntegrableOn Real.exp B ν)
    (hRate : 0 < (ν B).toReal) (t : ℝ) :
    Real.exp (t * ((ν B).toReal *
      ((∫ y in B, Real.exp y ∂ν) / (ν B).toReal - 1))) =
    Real.exp (-(t * (∫ y in B, (1 - Real.exp y) ∂ν))) := by
  rw [AvramDividend.Classical.avram_redux18_mark_compensator_subtract
    ν B hOne hExp]
  congr 1
  have hne : (ν B).toReal ≠ 0 := ne_of_gt hRate
  field_simp [hne]
  ring