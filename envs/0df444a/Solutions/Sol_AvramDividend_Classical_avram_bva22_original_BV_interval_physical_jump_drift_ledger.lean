-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva22_original_BV_interval_physical_jump_drift_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:17:42.503201+00:00
-- url     : https://prove2.me/submissions/07a2c26c-4b40-48a4-aa34-6b458bca7265

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
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
    ∀ᵐ ω ∂P, ∀ a b : ℝ≥0, a ≤ b →
      X.X b ω - X.X a ω = ((b : ℝ) - (a : ℝ)) * X.drift -
        (∑' u : ℝ≥0, if a < u ∧ u ≤ b then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by
  have hRaw := avram_redux11_original_BV_raw_removed_residual_zero_ae X hX hBV
  have hSummable :=
    avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV
  filter_upwards [hRaw, hSummable] with ω hω hsumω
  intro a b hab
  have hs0a := (hsumω 0 a (show (0 : ℝ≥0) ≤ a from zero_le)).1
  have hsab := (hsumω a b hab).1
  have hSplit :
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) =
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) +
      (∑' u : ℝ≥0, if a < u ∧ u ≤ b then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by
    rw [← Summable.tsum_add hs0a hsab]
    apply tsum_congr
    intro u
    by_cases h0 : 0 < u
    · by_cases ha : u ≤ a
      · have hb : u ≤ b := le_trans ha hab
        simp [h0, ha, hb, not_lt.mpr ha]
      · have hau : a < u := lt_of_not_ge ha
        by_cases hb : u ≤ b
        · simp [h0, ha, hau, hb]
        · simp [ha, hb]
    · have hau : ¬ a < u :=
        not_lt.mpr (le_trans (le_of_not_gt h0)
          (show (0 : ℝ≥0) ≤ a from zero_le))
      simp [h0, hau]
  have ha := hω a
  have hb := hω b
  rw [hSplit] at hb
  linear_combination ha - hb
