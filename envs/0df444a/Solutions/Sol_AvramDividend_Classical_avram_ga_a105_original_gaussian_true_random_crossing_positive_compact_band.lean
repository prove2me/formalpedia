-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a105_original_gaussian_true_random_crossing_positive_compact_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:51:56.26831+00:00
-- url     : https://prove2.me/submissions/ff851a0d-d5d6-4fbc-9423-9d31de58cc1c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Uniformly small original Gaussian random crossing increments preserve a genuine strictly positive source compact band. -/
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
      α ≤ y m ω ∧ y m ω ≤ β) :
    ∀ᵐ ω ∂P, ∀ᶠ m in atTop,
      y m ω ∈ Icc (α / 2) (β + α / 2) ∧
        y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ∈
          Icc (α / 2) (β + α / 2) := by
  have hAE := avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
    X hν T s t hRange hGap
  filter_upwards [hAE, hBase] with ω hInc hBounds
  have hSmall : ∀ᶠ m in atTop,
      |X.X (t m ω) ω - X.X (s m ω) ω| < α / 2 := by
    have hPos : 0 < α / 2 := by positivity
    obtain ⟨N,hN⟩ := (Metric.tendsto_atTop.1 hInc) (α / 2) hPos
    filter_upwards [Filter.eventually_ge_atTop N] with m hm
    simpa only [Real.dist_eq, sub_zero] using hN m hm
  filter_upwards [hBounds, hSmall] with m hY hS
  obtain ⟨hLow,hHigh⟩ := hY
  obtain ⟨hDeltaLow,hDeltaHigh⟩ := abs_lt.mp hS
  constructor
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩
