-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a104_original_gaussian_true_random_crossing_positive_compact_value_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:45:30.6287+00:00
-- url     : https://prove2.me/submissions/dace5e13-5d80-4daa-b9cb-3b15c4110b44

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_ga_a28_compact_modulus_last_increment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- True random stop-crossing original Gaussian value displacements vanish on an eventual positive reserve compact band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Icc 0 T ∧ t m ω ∈ Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1))
    (w : ℝ → ℝ) (a b : ℝ) (y : ℕ → Ω → ℝ)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, u ∈ Icc a b → v ∈ Icc a b →
        |v - u| < δ → |w v - w u| < ε)
    (hBand : ∀ᵐ ω ∂P, ∀ᶠ m in atTop,
      y m ω ∈ Icc a b ∧
        y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ∈ Icc a b) :
    ∀ᵐ ω ∂P, Tendsto (fun m =>
      w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)) atTop (𝓝 (0 : ℝ)) := by
  have hAE := avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
    X hν T s t hRange hGap
  filter_upwards [hAE, hBand] with ω hInc hPair
  have hy : ∀ᶠ m in atTop, y m ω ∈ Icc a b :=
    hPair.mono (fun m hm => hm.1)
  have hz : ∀ᶠ m in atTop,
      y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ∈ Icc a b :=
    hPair.mono (fun m hm => hm.2)
  have hd : Tendsto (fun m =>
      (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        y m ω) atTop (𝓝 (0 : ℝ)) := by
    convert hInc using 1
    funext m
    ring
  exact avram_ga_a28_compact_modulus_last_increment
    w a b (fun m => y m ω)
    (fun m => y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
    hmod hy hz hd
