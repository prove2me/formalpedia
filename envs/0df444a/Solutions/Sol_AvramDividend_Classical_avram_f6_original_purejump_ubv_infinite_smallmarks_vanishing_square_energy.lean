-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_purejump_ubv_infinite_smallmarks_vanishing_square_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:16:10.108373+00:00
-- url     : https://prove2.me/submissions/4f9b5271-82cc-4fcf-b500-440583ca7489

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_purejump_ubv_infinite_mass_each_small_negative_band
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_small_negative_jump_square_intensity_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) :
    (∀ δ : ℝ, 0 < δ → X.ν (Ioo (-δ) 0) = ⊤) ∧
    Tendsto (fun n : ℕ =>
      ∫⁻ z in Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)),
        ENNReal.ofReal (z ^ 2) ∂(X.ν.map (fun y : ℝ => -y)))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  constructor
  · intro δ hδ
    exact avram_f6_purejump_ubv_infinite_mass_each_small_negative_band
      X hBV hσ δ hδ
  · exact avram_wave4_04_source_small_negative_jump_square_intensity_tendsto_zero X
