-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva22_original_all_BV_two_clock_source_increment_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:09:16.037198+00:00
-- url     : https://prove2.me/submissions/92439643-f341-4743-a989-f47bd2ded9a0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ≥0,
      X.X b ω - X.X a ω =
        ((b : ℝ) - (a : ℝ)) * X.drift -
          ((∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) -
           (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) := by
  have hPath := avram_redux11_original_BV_raw_removed_residual_zero_ae X hX hBV
  filter_upwards [hPath] with ω hω
  intro a b
  have ha := hω a
  have hb := hω b
  linear_combination ha - hb
