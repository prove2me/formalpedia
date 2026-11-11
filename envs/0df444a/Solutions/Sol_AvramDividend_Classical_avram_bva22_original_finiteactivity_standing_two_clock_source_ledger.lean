-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva22_original_finiteactivity_standing_two_clock_source_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:05:41.734391+00:00
-- url     : https://prove2.me/submissions/bc4878c6-6d0c-480a-8584-b8e95c0c73b6

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_bva22_original_finite_activity_standing_exact_drift_jump_path
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
    (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ≥0, a ≤ b → b ≤ T →
      X.X b ω - X.X a ω =
        ((b : ℝ) - (a : ℝ)) * X.drift -
          ((∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) -
           (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) := by
  have hPath :=
    avram_bva22_original_finite_activity_standing_exact_drift_jump_path
      X hX hBV hActivity T hT
  filter_upwards [hPath] with ω hω
  intro a b hab hb
  have ha := hω a (le_trans hab hb)
  have hb' := hω b hb
  linear_combination ha - hb'
