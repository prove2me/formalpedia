-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_uniform_CP_standing_BV_drift_one_source_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:26:13.637372+00:00
-- url     : https://prove2.me/submissions/3f38dabd-1c57-44c4-8ec9-b306afab41d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_driver_on_real_sequence_product
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_poisson_triplet
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_measure_facts
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_bv_moments
import Theorems.Thm_AvramDividend_Classical_avram_a06_bv_standing_from_diffuse_positive_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
theorem solution :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.BoundedVariation ∧
      X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0) ∧
      X.ν (Iio (0 : ℝ)) < ⊤ ∧ X.drift = 1 ∧ X.σ = 0 := by
  obtain ⟨P, τ, Y, hP, hd⟩ :=
    avram_a06_uniform_driver_on_real_sequence_product
  letI : IsProbabilityMeasure P := hP
  obtain ⟨𝓕, X, hσ, hν, hc, hL1⟩ :=
    avram_a06_original_compound_poisson_triplet P τ Y hd
  have hfacts := avram_a06_uniform_negative_mark_measure_facts
  have hbv : X.BoundedVariation := by
    constructor
    · exact hσ
    · simpa [hν] using avram_a06_uniform_negative_mark_bv_moments.2
  have hdrift : X.drift = 1 := by
    change X.c - ∫ y in Ioo (-1 : ℝ) 0, y ∂X.ν = 1
    rw [hc, hν]
    ring
  have hnonzero : X.ν ≠ 0 := by
    simpa [hν] using hfacts.2.2.2.1
  have hdiffuse : X.ν ≪ volume := by
    simpa [hν] using hfacts.2.2.2.2
  have hstanding : X.Standing :=
    avram_a06_bv_standing_from_diffuse_positive_drift
      X (by rw [hdrift]; norm_num) hnonzero hL1 hdiffuse
  refine ⟨P, 𝓕, X, hstanding, hbv, hν, ?_, hdrift, hσ⟩
  simpa [hν] using hfacts.2.2.1
