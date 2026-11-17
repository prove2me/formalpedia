-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB31_concrete_gaussian_source_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T17:51:12.634319+00:00
-- url     : https://prove2.me/submissions/7cffdf23-a768-42be-9de9-e2d4da8e3f56

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_positive_gaussian_original_HJB_source
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
  obtain ⟨𝓕, Y, _, _, _, hStand, hUBV, hGen⟩ :=
    avram_gbB30_positive_gaussian_original_HJB_source
  obtain ⟨hzero, hcont, hneg, hC2⟩ :=
    avram_gbB30_original_source_quad_regularity
  obtain ⟨hAdm, _⟩ :=
    avram_gbB30_original_barrier_no_initial_atom_source
      Y (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2)
      (1 / 8 : ℝ) (1 / 8 : ℝ)
      (by norm_num) (by norm_num) (le_refl _)
  exact ⟨𝓕, Y, hStand, hUBV, hzero, hcont, hneg,
    hC2, hGen, hAdm⟩
