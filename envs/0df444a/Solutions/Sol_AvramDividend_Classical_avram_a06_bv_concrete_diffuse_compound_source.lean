-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_bv_concrete_diffuse_compound_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:07:55.246531+00:00
-- url     : https://prove2.me/submissions/70e56332-f041-4533-9518-b8a979667f8a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_driver_on_real_sequence_product
import Theorems.Thm_AvramDividend_Classical_avram_a06_bv_compound_driver_to_original_source

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- Construct the literal A06 fixed-product source from the independent
compound-Poisson driver and its original filtered Lévy-process adapter. -/
theorem solution :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
        X.BoundedVariation ∧
        X.ν (Iio (0 : ℝ)) < ⊤ ∧
        0 < X.drift ∧
        X.ν ≠ 0 ∧
        Integrable (X.X 1) P ∧
        X.ν ≪ volume := by
  obtain ⟨P, τ, Y, hP, hd⟩ :=
    AvramDividend.Classical.avram_a06_uniform_driver_on_real_sequence_product
  letI : IsProbabilityMeasure P := hP
  obtain ⟨𝓕, X, hBV, hfinite, hpositive, hnonzero, hL1, hdiffuse⟩ :=
    AvramDividend.Classical.avram_a06_bv_compound_driver_to_original_source
      P τ Y hd
  exact ⟨P, 𝓕, X, hBV, hfinite, hpositive, hnonzero, hL1, hdiffuse⟩
