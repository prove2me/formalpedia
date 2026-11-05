-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_original_negative_source_eq_auto_unit_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:22:06.576202+00:00
-- url     : https://prove2.me/submissions/7184e122-61a5-4f68-972c-eefebe88a041

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_original_negative_source_eq_of_candidate_moments
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_negative_exp_fourth_weighted_image_unit_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Moment identification of an original negative Levy source represented by
a candidate measure: the image support follows from negative marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (η ρ σ : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ρ] [η.Regular] [ρ.Regular]
    (hη : η = (((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))
    (hρ : ρ = ((σ.withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))
    (hnegσ : ∀ᵐ y ∂σ, y < 0)
    (hne : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hmomρ : ∀ k, Tendsto (fun h : ℝ =>
      ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
        (if 0 < h then (ENNReal.ofReal h)⁻¹ •
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
         else (0 : Measure ℝ)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ρ))) :
    X.ν.restrict (Iio (0 : ℝ)) = σ := by
  have hunitρ : ∀ᵐ z ∂ρ, z ∈ Icc (0 : ℝ) 1 := by
    rw [hρ]
    exact avram_p2_m_uniqueness_negative_exp_fourth_weighted_image_unit_support
      σ hnegσ
  exact avram_p2_m_uniqueness_original_negative_source_eq_of_candidate_moments
    X η ρ σ hη hρ hnegσ hne hunitρ hmomρ
