-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva21_negative_mark_restrict_indicator_extract
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T21:54:06.446051+00:00
-- url     : https://prove2.me/submissions/0eea6fcd-f0af-4aa8-9bcd-b897fadde6bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
noncomputable section

/-- On negative marks the mark sign indicator is redundant, and scalar masks factor out. -/
theorem solution
    (μ : MeasureTheory.Measure ℝ) (f : ℝ → ℝ)
    (c : ℝ) (guard : Prop) :
    (∫ z : ℝ, (if guard ∧ z < 0 then c * f z else 0)
      ∂(μ.restrict (Set.Iio (0 : ℝ)))) =
    if guard then c * (∫ z in Set.Iio (0 : ℝ), f z ∂μ) else 0 := by
  classical
  have hAE : ∀ᵐ z ∂(μ.restrict (Iio (0 : ℝ))), z < 0 := by
    simpa only [mem_Iio] using
      (ae_restrict_mem (μ := μ) (s := Iio (0 : ℝ)) measurableSet_Iio)
  calc
    (∫ z : ℝ, (if guard ∧ z < 0 then c * f z else 0)
      ∂(μ.restrict (Iio (0 : ℝ)))) =
        ∫ z : ℝ, (if guard then c * f z else 0)
          ∂(μ.restrict (Iio (0 : ℝ))) := by
      apply integral_congr_ae
      filter_upwards [hAE] with z hz
      simp [hz]
    _ = if guard then c * (∫ z in Iio (0 : ℝ), f z ∂μ) else 0 := by
      by_cases h : guard
      · simp [h, integral_const_mul]
      · simp [h]
