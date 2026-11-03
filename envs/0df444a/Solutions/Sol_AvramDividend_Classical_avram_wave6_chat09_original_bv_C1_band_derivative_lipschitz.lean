-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:32:32.33838+00:00
-- url     : https://prove2.me/submissions/55e28c3e-335c-43ec-9794-ef1a2774e70a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |w s - w t| ≤ (K : ℝ) * |s - t| := by
  have hDiff : ∀ y ∈ Icc a b, DifferentiableAt ℝ w y := by
    intro y hy
    have hd := (hwC1 hBV).differentiableOn_one y (hBand hy)
    exact hd.differentiableAt (hOpen.mem_nhds (hBand hy))
  have hLip : LipschitzOnWith K w (Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le hDiff hK
  intro s hs t ht
  simpa only [Real.dist_eq] using hLip.dist_le_mul s hs t ht
