-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_compound_poisson_triplet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:41:17.96978+00:00
-- url     : https://prove2.me/submissions/2f8761a0-6bc9-4c72-8593-0dfa036c3724

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compoundPoisson_filtered_law_core
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_one_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original triplet follows from an exact filtered Lévy modification of
the compound-Poisson path and its independently proved first-moment bound. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∃ (𝓕 : Filtration ℝ≥0
      (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
        X.σ = 0 ∧
        X.ν = ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) ∧
        X.c = (1 : ℝ) +
          (∫ y in Ioo (-1 : ℝ) 0,
            y ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) ∧
        Integrable (X.X 1) P := by
  obtain ⟨𝓕, X, hσ, hν, hc, hLaw⟩ :=
    AvramDividend.Classical.avram_a06_original_compoundPoisson_filtered_law_core
      P τ Y hd
  refine ⟨𝓕, X, hσ, hν, hc, ?_⟩
  have hcp :=
    AvramDividend.Classical.avram_a06_compoundPoisson_one_integrable hd
  exact hcp.congr (hLaw 1).symm
