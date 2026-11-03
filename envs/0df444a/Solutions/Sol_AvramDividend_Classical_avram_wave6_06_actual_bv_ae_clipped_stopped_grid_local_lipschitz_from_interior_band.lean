-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_actual_bv_ae_clipped_stopped_grid_local_lipschitz_from_interior_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:47:25.305396+00:00
-- url     : https://prove2.me/submissions/8e77e51e-d347-4215-ba00-1d13a8aa6564

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_finite_cap_local_C1_lipschitz

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (w : ℝ → ℝ) (cap : ℝ)
    (hwC1 : X.BoundedVariation → ContDiffOn ℝ 1 w (Ioo 0 cap))
    (hInterior : ∀ᵐ ω ∂P, ∃ a b : ℝ,
      a < b ∧ Icc a b ⊆ Ioo 0 cap ∧
      (∀ n i, i < k n →
        x + X.X (min (u n (i + 1)) (τ ω)) ω -
          rightLimit D (min (u n i) (τ ω)) ω ∈ Icc a b) ∧
      (∀ n i, i < k n →
        x + X.X (min (u n (i + 1)) (τ ω)) ω -
          rightLimit D (min (u n (i + 1)) (τ ω)) ω ∈ Icc a b)) :
    ∀ᵐ ω ∂P, ∃ L a b : ℝ,
      0 ≤ L ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        |w s - w t| ≤ L * |s - t|) ∧
      (∀ n i, i < k n →
        x + X.X (min (u n (i + 1)) (τ ω)) ω -
          rightLimit D (min (u n i) (τ ω)) ω ∈ Icc a b) ∧
      (∀ n i, i < k n →
        x + X.X (min (u n (i + 1)) (τ ω)) ω -
          rightLimit D (min (u n (i + 1)) (τ ω)) ω ∈ Icc a b) := by
  filter_upwards [hInterior] with ω hω
  rcases hω with ⟨a, b, hab, hsub, hpre, hpost⟩
  obtain ⟨L, hL0, hLip⟩ :=
    avram_wave6_chat09_original_bv_finite_cap_local_C1_lipschitz
      X hBV w cap a b hab hsub hwC1
  exact ⟨L, a, b, hL0, hLip, hpre, hpost⟩
