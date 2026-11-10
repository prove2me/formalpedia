-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_finite734_fullcap_negative_mark_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T18:36:22.149568+00:00
-- url     : https://prove2.me/submissions/d1f4dfef-13c2-49e4-afa2-739ab73fc6e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_finite734_original_negative_mark_oscillation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

-- The finite cap lets the previously certified closed-band mark bound reach both endpoints.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hactivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (hFinite : C ≠ ⊤) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y z : ℝ, y ∈ Icc (0 : ℝ) C.toReal → z < 0 →
        |w (y + z) - w y| ≤ K := by
  have hCtop : C < ⊤ := lt_top_iff_ne_top.mpr hFinite
  have hCpos : 0 < C.toReal := (ENNReal.toReal_pos_iff).2 ⟨hC, hCtop⟩
  have hCcast : ENNReal.ofReal C.toReal ≤ C := by
    rw [ENNReal.ofReal_toReal hFinite]
  obtain ⟨K, hK, hbound⟩ :=
    avram_bv_finite734_original_negative_mark_oscillation
      X hX hBV q hq w C hC hw_cont hw0 hw_neg
      hw_smooth hw_gen hw_grad hactivity C.toReal hCpos hCcast
  exact ⟨K, hK, hbound⟩
