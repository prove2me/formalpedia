-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_original_negative_source_eq_of_candidate_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:01:38.714803+00:00
-- url     : https://prove2.me/submissions/03b6dfe7-7a30-44f0-bd7e-b667fc4e0991

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_original_levy_image_eq_of_finite_unit_moments
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_negative_exp_fourth_weighted_source_measure_ext

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A genuine original-process moment candidate represented by a strictly
negative source measure identifies the original restricted Levy measure
on all Borel sets, with no marked-count intensity premise. -/
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
    (hunitρ : ∀ᵐ z ∂ρ, z ∈ Icc (0 : ℝ) 1)
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
  have hmeasure : η = ρ :=
    avram_p2_m_uniqueness_original_levy_image_eq_of_finite_unit_moments
      X η ρ hη hne hunitρ hmomρ
  have hnegative : ∀ᵐ y ∂(X.ν.restrict (Iio (0 : ℝ))), y < 0 := by
    exact (ae_restrict_mem measurableSet_Iio).mono (fun y hy => hy)
  apply avram_p2_m_uniqueness_negative_exp_fourth_weighted_source_measure_ext
    (X.ν.restrict (Iio (0 : ℝ))) σ hnegative hnegσ
  exact hη.symm.trans (hmeasure.trans hρ)
