-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18j_finite_activity_countable_real_model_square
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:07:49.619887+00:00
-- url     : https://prove2.me/submissions/07c6898e-ada5-4604-9f8c-8e57b0b33b27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja19_finite_activity_companion_square_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_ja19_square_integrable_of_ae_sum_components
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (t : ℝ≥0) :
    ∃ (P₂ : Measure (ℕ → ℝ))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ)))
      (Y : SpectrallyNegativeLevy P₂ 𝓕₂),
      X.c = Y.c ∧ X.σ = Y.σ ∧ X.ν = Y.ν ∧
      Integrable (fun ω : ℕ → ℝ =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual Y 0 t ω) ^ 2) P₂ := by
  obtain ⟨P₂, 𝓕₂, Y, G, J, hc, hσ, hν, hG, hJ, heq⟩ :=
    avram_ja19_finite_activity_companion_square_decomposition X hX hFinite t
  refine ⟨P₂, 𝓕₂, Y, hc, hσ, hν, ?_⟩
  have hmeas : Measurable (fun ω : ℕ → ℝ =>
      avram_p4_h_gaussian_intrinsic_truncated_residual Y 0 t ω) :=
    (avram_mix_gauss14_original_intrinsic_truncated_residual_adapted Y 0 t).mono
      (𝓕₂.le t) le_rfl
  exact avram_ja19_square_integrable_of_ae_sum_components
    (fun ω : ℕ → ℝ =>
      avram_p4_h_gaussian_intrinsic_truncated_residual Y 0 t ω)
    G J hmeas.aestronglyMeasurable hG hJ heq
