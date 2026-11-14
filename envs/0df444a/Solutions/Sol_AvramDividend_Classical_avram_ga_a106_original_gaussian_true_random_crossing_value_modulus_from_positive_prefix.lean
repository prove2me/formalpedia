-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a106_original_gaussian_true_random_crossing_value_modulus_from_positive_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:13:24.261217+00:00
-- url     : https://prove2.me/submissions/c3162f72-2c1d-4a52-80a4-0ff9b1530b45

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a104_original_gaussian_true_random_crossing_positive_compact_value_modulus
import Theorems.Thm_AvramDividend_Classical_avram_ga_a105_original_gaussian_true_random_crossing_positive_compact_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Positive compact-band local modulus for the true randomly stopped Gaussian source follows from proved original band preservation and compact modulus. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Icc 0 T ∧ t m ω ∈ Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1))
    (α β : ℝ) (hα : 0 < α) (y : ℕ → Ω → ℝ)
    (hBase : ∀ᵐ ω ∂P, ∀ᶠ m in atTop,
      α ≤ y m ω ∧ y m ω ≤ β)
    (w : ℝ → ℝ)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ,
        u ∈ Icc (α / 2) (β + α / 2) →
        v ∈ Icc (α / 2) (β + α / 2) →
        |v - u| < δ → |w v - w u| < ε) :
    ∀ᵐ ω ∂P, Tendsto (fun m =>
      w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)) atTop (𝓝 (0 : ℝ)) := by
  have hBand :=
    avram_ga_a105_original_gaussian_true_random_crossing_positive_compact_band
      X hν T s t hRange hGap α β hα y hBase
  exact avram_ga_a104_original_gaussian_true_random_crossing_positive_compact_value_modulus
    X hν T s t hRange hGap w (α / 2) (β + α / 2) y hmod hBand
