-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_allcap_original_stopped_positive_no_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:59:42.08534+00:00
-- url     : https://prove2.me/submissions/8e387f3c-90e9-4bfe-b9d7-a96e722bb0b7

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_allcap_actual_generator_interior_no_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0∞)
    (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < σ ω) →
        0 < riskProcess X x D t ω := by
  have hDtop : IsAdmissibleLe X x (⊤ : ℝ≥0∞) D := by
    refine ⟨hD.1, ?_⟩
    intro ω t ht
    exact le_top
  have hocc := avram_wave4_04_ubv_allcap_actual_generator_interior_no_grid
    X hBV x (⊤ : ℝ≥0∞) (by simp) D hDtop (le_top) μ
  filter_upwards [hocc] with ω hω
  filter_upwards [hω] with t ht
  intro htime
  exact (ht ⟨htime.1, lt_of_lt_of_le htime.2 (hσ ω)⟩).1
