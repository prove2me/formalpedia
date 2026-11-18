-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB133_original_gaussian_full_HJB_admissible_witness_with_exact_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:46:59.870832+00:00
-- url     : https://prove2.me/submissions/4e580092-c60b-4f60-9970-0fc7eb378a62

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB132_original_positive_gaussian_standing_witness_with_exact_path
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_original_gaussian_generator_quadjet
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_piecewise_first_derivative
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_piecewise_second_derivative
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_original_source_quad_regularity
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_original_barrier_no_initial_atom_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution :
    ∃ (𝓕 : Filtration ℝ≥0 (inferInstance :
        MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      (0 ≤ (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) 0) ∧ ContinuousOn (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) (Ici 0) ∧
      (∀ y : ℝ, y < 0 → (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y = 0) ∧
      ContDiffOn ℝ 2 (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2)
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal (1 / 8 : ℝ)} ∧
      (∀ y : ℝ, 0 < y → y < (1 / 8 : ℝ) →
        Y.GeneratorIntegrable (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y ∧
        Y.generator (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y - (1 / 100 : ℝ) * (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y ≤ 0 ∧
        1 ≤ deriv (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y) ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) := by
  obtain ⟨𝓕, Y, hYpath, hYc, hYσ, hYν, hStand, hUBV⟩ :=
    avram_gbB132_original_positive_gaussian_standing_witness_with_exact_path
  have hGen : ∀ y : ℝ, 0 < y → y < (1 / 8 : ℝ) →
      Y.GeneratorIntegrable (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y ∧
      Y.generator (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y -
        (1 / 100 : ℝ) * (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y ≤ 0 ∧
      1 ≤ deriv (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y := by
    intro y hy hyC
    let w : ℝ → ℝ :=
      fun u => if u < 0 then 0 else 2 * u - 4 * u ^ 2
    have hw0 : w y = 2 * y - 4 * y ^ 2 := by
      simp [w, not_lt.mpr (le_of_lt hy)]
    have hw1 := avram_gbB30_piecewise_first_derivative y hy
    have hw2 := avram_gbB30_piecewise_second_derivative y hy
    obtain ⟨hInt, heq⟩ :=
      avram_gbB30_original_gaussian_generator_quadjet
        Y hYν hYσ hYc w y hw0 hw1 hw2
    refine ⟨hInt, ?_, ?_⟩
    · rw [heq]
      nlinarith [mul_nonneg (le_of_lt hy)
        (sub_nonneg.mpr (le_of_lt hyC))]
    · change 1 ≤ deriv w y
      rw [hw1]
      linarith
  obtain ⟨hzero, hcont, hneg, hC2⟩ :=
    avram_gbB30_original_source_quad_regularity
  obtain ⟨hAdm, _⟩ :=
    avram_gbB30_original_barrier_no_initial_atom_source
      Y (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2)
      (1 / 8 : ℝ) (1 / 8 : ℝ)
      (by norm_num) (by norm_num) (le_refl _)
  exact ⟨𝓕, Y, hYpath, hStand, hUBV, hzero, hcont, hneg,
    hC2, hGen, hAdm⟩
