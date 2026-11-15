-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB65_original_smooth_compact_band_all_fullcell_value_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:09:55.401752+00:00
-- url     : https://prove2.me/submissions/90fda121-c055-46d7-9c16-32832c406c0b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB64_original_gaussian_compact_band_all_fullcell_spatial_value_modulus
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_band_lipschitz_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
        ∀ i : ℕ, i < m →
          let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
          let s : ℝ≥0 := (i : ℝ≥0) * Δ
          x + X.X s ω - rightLimit D s ω ∈ Icc δ K →
          x + X.X (s + Δ) ω - rightLimit D s ω ∈ Icc δ K →
          |w (x + X.X (s + Δ) ω - rightLimit D s ω) -
            w (x + X.X s ω - rightLimit D s ω)| < ε := by
  obtain ⟨B, hBound⟩ :=
    avram_p4_f3_original_positive_band_lipschitz_source
      w C hw_smooth δ K hδ hδK hK
  let L : ℝ := max B 0
  have hL : 0 ≤ L := le_max_right B 0
  have hLip : ∀ u ∈ Icc δ K, ∀ v ∈ Icc δ K,
      |w v - w u| ≤ L * |v - u| := by
    intro u hu v hv
    calc
      |w v - w u| ≤ B * |v - u| := hBound u hu v hv
      _ ≤ L * |v - u| :=
        mul_le_mul_of_nonneg_right (le_max_left B 0) (abs_nonneg _)
  exact avram_gbB64_original_gaussian_compact_band_all_fullcell_spatial_value_modulus
    X hν x D w δ K L hL hLip n
