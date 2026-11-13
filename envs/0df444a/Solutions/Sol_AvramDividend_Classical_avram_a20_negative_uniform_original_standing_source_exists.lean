-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_negative_uniform_original_standing_source_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T07:43:04.173914+00:00
-- url     : https://prove2.me/submissions/1aad3252-dd05-45ea-b643-84f56f382b74

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_driver_on_real_sequence_product
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_poisson_triplet
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_measure_facts
import Theorems.Thm_AvramDividend_Classical_avram_a06_bv_standing_from_diffuse_positive_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- A genuine source-exact positive-drift original filtered Lévy process with the unit negative-uniform marks. -/
theorem solution :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧
      X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0) ∧
      X.ν (Iio (0 : ℝ)) < ⊤ := by
  obtain ⟨P, τ, Y, hP, hd⟩ :=
    avram_a06_uniform_driver_on_real_sequence_product
  letI : IsProbabilityMeasure P := hP
  obtain ⟨𝓕, X, hσ, hν, hc, hL1⟩ :=
    avram_a06_original_compound_poisson_triplet P τ Y hd
  have hfacts := avram_a06_uniform_negative_mark_measure_facts
  have hdrift : 0 < X.drift := by
    change 0 < X.c - ∫ y in Ioo (-1 : ℝ) 0, y ∂X.ν
    rw [hc, hν]
    have hcancel (a : ℝ) : (1 : ℝ) + a - a = 1 := by ring
    rw [hcancel]
    norm_num
  have hnonzero : X.ν ≠ 0 := by
    simpa [hν] using hfacts.2.2.2.1
  have hdiffuse : X.ν ≪ volume := by
    simpa [hν] using hfacts.2.2.2.2
  have hstanding : X.Standing :=
    avram_a06_bv_standing_from_diffuse_positive_drift
      X hdrift hnonzero hL1 hdiffuse
  refine ⟨P, 𝓕, X, hstanding, hν, ?_⟩
  simpa [hν] using hfacts.2.2.1
