-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_any_interior_C1_band_automatic_negative_mark_compensator_analytic_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:26:51.109234+00:00
-- url     : https://prove2.me/submissions/7c691532-bccf-4196-b003-b6fd3f47643e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_C1_compact_band_automatic_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hinside : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ L R : ℝ,
      0 ≤ L ∧ 0 ≤ R ∧
      (∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
        |w u - w v| ≤ L * |u - v|) ∧
      (∀ v : ℝ, v ≤ b → |w v| ≤ R) ∧
      X.ν (Iic (-a / 2)) < ⊤ := by
  have hband : a / 2 ≤ b := by linarith
  obtain ⟨L, hL⟩ :=
    avram_wave8_22_original_BV_C1_compact_band_automatic_lipschitz
      X hBV C w hw_smooth (a / 2) b hband hinside
  have hbnonneg : 0 ≤ b := le_trans (le_of_lt ha) hab
  obtain ⟨R, hR, hBound⟩ :=
    avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
      w hw_cont hw_neg b hbnonneg
  refine ⟨(L : ℝ), R, NNReal.coe_nonneg L, hR, ?_, hBound, ?_⟩
  · intro u hu v hv
    exact hL u hu v hv
  · exact
      avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
        X a ha ha2
