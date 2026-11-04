-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_original_negative_compact_test_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:19:04.958575+00:00
-- url     : https://prove2.me/submissions/b428fced-13f1-4006-820b-9e2aa9ff9eec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_original_levy_weighted_log_test_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_weighted_log_image_integral_eq_source_test

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Actual original compact-negative test expectation has the genuine source Lévy small-time rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0) :
    Tendsto (fun h : ℝ => if 0 < h then
      ((ENNReal.ofReal h)⁻¹).toReal *
        (∫ ω, f (X.X (Real.toNNReal h) ω) ∂P)
      else 0)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ))))) := by
  have hfpos : ∀ y : ℝ, 0 ≤ y → f y = 0 := by
    intro y hy
    apply hfupper y
    linarith
  have hYm (h : ℝ) : Measurable (X.X (Real.toNNReal h)) :=
    (X.adapted (Real.toNNReal h)).mono (𝓕.le _) le_rfl
  have hsource :=
    avram_p2_i_moment_original_levy_weighted_log_test_tendsto
      X f hf a ε hε hflower hfupper
  have hleft :
      (fun h : ℝ => ∫ z : ℝ, f (Real.log z) / (z - 1) ^ 4 ∂
        (if 0 < h then (ENNReal.ofReal h)⁻¹ •
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
         else (0 : Measure ℝ))) =
      (fun h : ℝ => if 0 < h then
        ((ENNReal.ofReal h)⁻¹).toReal *
          (∫ ω, f (X.X (Real.toNNReal h) ω) ∂P)
        else 0) := by
    funext h
    by_cases hh : 0 < h
    · have hchange :=
        avram_p2_i_moment_weighted_log_image_integral_eq_source_test
          P (X.X (Real.toNNReal h)) (hYm h) f hf.measurable hfpos
      simpa only [if_pos hh, integral_smul_measure, smul_eq_mul] using
        congrArg (fun t : ℝ => ((ENNReal.ofReal h)⁻¹).toReal * t) hchange
    · simp [hh]
  have hright :
      (∫ z : ℝ, f (Real.log z) / (z - 1) ^ 4 ∂
        (((X.ν.restrict (Iio (0 : ℝ))).withDensity
          (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp)) =
      (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ)))) := by
    exact avram_p2_i_moment_weighted_log_image_integral_eq_source_test
      (X.ν.restrict (Iio (0 : ℝ))) (fun y : ℝ => y)
      measurable_id f hf.measurable hfpos
  rw [hleft, hright] at hsource
  exact hsource
