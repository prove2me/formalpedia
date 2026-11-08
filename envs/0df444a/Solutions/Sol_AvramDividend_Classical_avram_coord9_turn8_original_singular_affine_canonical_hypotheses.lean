-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord9_turn8_original_singular_affine_canonical_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T00:36:35.951974+00:00
-- url     : https://prove2.me/submissions/0d83191a-00e8-4153-a9a2-cfff48b9933b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_zero_extension_boundary
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_zero_extension_smooth
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_zero_extension_deriv_one
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_global_positive_reserve_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_original_generator_discount_one_le_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An exact source singular Lévy triplet supplies all canonical affine
    verification test-function hypotheses at every positive reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hc : X.c = 0) (C : ℝ≥0∞) :
    let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 + y
    ContinuousOn w (Ici 0) ∧
      0 ≤ w 0 ∧
      (∀ y : ℝ, y < 0 → w y = 0) ∧
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        X.GeneratorIntegrable w y ∧ X.generator w y - 1 * w y ≤ 0) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) := by
  dsimp only
  obtain ⟨hcont, hzero, hnegative⟩ :=
    avram_a19_affine_zero_extension_boundary
  refine ⟨hcont, hzero, hnegative,
    avram_a19_affine_zero_extension_smooth C, ?_, ?_⟩
  · intro y hy _
    refine ⟨avram_a19_affine_singular_global_positive_reserve_integrable
      X hν y hy, ?_⟩
    simpa only [one_mul] using
      (avram_a19_affine_singular_original_generator_discount_one_le_zero
        X hBV hν hc y hy)
  · intro y hy _
    rw [avram_a19_affine_zero_extension_deriv_one y hy]
