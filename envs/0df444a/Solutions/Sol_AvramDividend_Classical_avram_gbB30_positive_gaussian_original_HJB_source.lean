-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB30_positive_gaussian_original_HJB_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T17:36:14.807777+00:00
-- url     : https://prove2.me/submissions/904a9479-a5f9-4b2d-a9d3-6df18ac47292

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_positive_gaussian_witness_standing
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_original_gaussian_generator_quadjet
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_piecewise_first_derivative
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_piecewise_second_derivative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      Y.c = 2 ∧ Y.σ = 1 ∧ Y.ν = 0 ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      (∀ y : ℝ, 0 < y → y < (1 / 8 : ℝ) →
        Y.GeneratorIntegrable (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y ∧
        Y.generator (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y -
          (1 / 100 : ℝ) * (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y ≤ 0 ∧
        1 ≤ deriv (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y) := by 
  obtain ⟨𝓕, Y, hYc, hYσ, hYν, hStanding, hUBV⟩ :=
    avram_gbB30_positive_gaussian_witness_standing
  refine ⟨𝓕, Y, hYc, hYσ, hYν, hStanding, hUBV, ?_⟩
  intro y hy hyC
  let w : ℝ → ℝ :=
    fun u => if u < 0 then 0 else 2 * u - 4 * u ^ 2
  have hw0 : w y = 2 * y - 4 * y ^ 2 := by
    simp [w, not_lt.mpr (le_of_lt hy)]
  have hw1 := avram_gbB30_piecewise_first_derivative y hy
  have hw2 := avram_gbB30_piecewise_second_derivative y hy
  have hgen :=
    avram_gbB30_original_gaussian_generator_quadjet
      Y hYν hYσ hYc w y hw0 hw1 hw2
  obtain ⟨hInt, heq⟩ := hgen
  refine ⟨hInt, ?_, ?_⟩
  · rw [heq]
    nlinarith [mul_nonneg (le_of_lt hy)
      (sub_nonneg.mpr (le_of_lt hyC))]
  · change 1 ≤ deriv w y
    rw [hw1]
    linarith
