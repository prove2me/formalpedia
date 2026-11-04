-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_C1_compact_band_automatic_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:22:25.554468+00:00
-- url     : https://prove2.me/submissions/b0215058-fa61-431b-abc3-d4209fba609e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_compact_cap_nnnorm_derivative_bound_automatic
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_compact_derivative_implies_lipschitz
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original positive-cap BV C¹ candidate is automatically Lipschitz on
every genuine interior compact reserve strip; no separate Lipschitz constant is assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ L : ℝ≥0, ∀ u ∈ Icc a b, ∀ v ∈ Icc a b,
      |w u - w v| ≤ (L : ℝ) * |u - v| := by
  obtain ⟨L, hDeriv⟩ :=
    avram_wave7_02_original_BV_C1_compact_cap_nnnorm_derivative_bound_automatic
      X hBV C w hwC1 a b hab hBand
  have hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen C
  have hDiff : ∀ y ∈ Icc a b, DifferentiableAt ℝ w y := by
    intro y hy
    have hyS : y ∈ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := hBand hy
    exact (hwC1.contDiffAt (hOpen.mem_nhds hyS)).differentiableAt (by norm_num)
  exact ⟨L,
    avram_wave8_22_original_BV_compact_derivative_implies_lipschitz
      w a b L hDiff hDeriv⟩
