-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_bv_compound_driver_to_original_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:36:01.592759+00:00
-- url     : https://prove2.me/submissions/19b46b7b-b691-4b2a-92be-0991c226271e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_poisson_triplet
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_measure_facts
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_bv_moments

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- Assemble the true source-exact stochastic triplet into the A06
original-process record with finite negative activity and positive drift. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∃ (𝓕 : Filtration ℝ≥0
      (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
        X.BoundedVariation ∧
        X.ν (Iio (0 : ℝ)) < ⊤ ∧
        0 < X.drift ∧
        X.ν ≠ 0 ∧
        Integrable (X.X 1) P ∧
        X.ν ≪ volume := by
  obtain ⟨𝓕, X, hσ, hν, hc, hL1⟩ :=
    AvramDividend.Classical.avram_a06_original_compound_poisson_triplet P τ Y hd
  have hfacts :=
    AvramDividend.Classical.avram_a06_uniform_negative_mark_measure_facts
  have hBV : X.BoundedVariation := by
    change X.σ = 0 ∧
      (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) < ⊤
    exact ⟨hσ, by simpa [hν] using
      AvramDividend.Classical.avram_a06_uniform_negative_mark_bv_moments.2⟩
  have hdrift : 0 < X.drift := by
    change 0 < X.c - ∫ y in Ioo (-1 : ℝ) 0, y ∂X.ν
    rw [hc, hν]
    have hcancel (a : ℝ) : (1 : ℝ) + a - a = 1 := by ring
    rw [hcancel]
    norm_num
  exact ⟨𝓕, X, hBV,
    by simpa [hν] using hfacts.2.2.1,
    hdrift,
    by simpa [hν] using hfacts.2.2.2.1,
    hL1,
    by simpa [hν] using hfacts.2.2.2.2⟩