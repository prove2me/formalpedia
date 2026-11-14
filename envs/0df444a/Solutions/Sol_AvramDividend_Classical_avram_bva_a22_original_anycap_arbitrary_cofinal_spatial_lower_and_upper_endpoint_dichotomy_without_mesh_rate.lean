-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_anycap_arbitrary_cofinal_spatial_lower_and_upper_endpoint_dichotomy_without_mesh_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:35:43.736226+00:00
-- url     : https://prove2.me/submissions/6db88430-286e-4dcc-9f3d-46bf29d32282

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_arbitrary_cofinal_positive_spatial_lower_band_tendsto_zero_without_rate
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_finitecap_arbitrary_cofinal_spatial_upper_band_tendsto_cap_without_rate
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_infinitecap_arbitrary_cofinal_spatial_upper_band_tendsto_infinity_without_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hab : ∀ n, a n ≤ b n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    Tendsto a atTop (𝓝 (0 : ℝ)) ∧
    (∀ L : ℝ, 0 < L → C = ENNReal.ofReal L →
      Tendsto b atTop (𝓝 L)) ∧
    (C = ⊤ → Tendsto b atTop atTop) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      avram_bva_a22_original_arbitrary_cofinal_positive_spatial_lower_band_tendsto_zero_without_rate
        C hC a b ha hab hinside hcover
  · intro L hL hCL
    exact
      avram_bva_a22_original_finitecap_arbitrary_cofinal_spatial_upper_band_tendsto_cap_without_rate
        C L hL hCL a b ha hab hinside hcover
  · intro hTop
    exact
      avram_bva_a22_original_infinitecap_arbitrary_cofinal_spatial_upper_band_tendsto_infinity_without_rate
        C hTop a b hcover
