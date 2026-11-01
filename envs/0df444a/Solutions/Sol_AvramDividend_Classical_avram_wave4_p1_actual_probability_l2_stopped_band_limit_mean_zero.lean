-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_actual_probability_l2_stopped_band_limit_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:11:54.992043+00:00
-- url     : https://prove2.me/submissions/dd17dffb-7406-49f3-9b2a-0df5fbbe67cc

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_band_centered_l2_limit_preserves_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_probability_l2_expectation_continuous_original_space

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem solution
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure α)
    (f : α → ℝ) (hf : Measurable f)
    (henergy : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ < ∞)
    (B : ℕ → Set α) (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, μ (B n) < ∞)
    (hBmono : Monotone B) (hBcover : (⋃ n, B n) = Set.univ)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hfinite_band_isometry_bound :
      ∀ m n, m ≤ n →
        dist (M m) (M n) ≤
          (eLpNorm ((B m)ᶜ.indicator f) (2 : ℝ≥0∞) μ).toReal)
    (hcentered : ∀ n, ∫ ω, (M n) ω ∂P = 0) :
    ∃ Mlimit : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (nhds Mlimit) ∧
      (∫ ω, Mlimit ω ∂P) = 0 := by
  exact
    AvramDividend.Classical.avram_wave4_p1_finite_band_centered_l2_limit_preserves_zero_mean
      μ f hf henergy B hB hBfinite hBmono hBcover
      M hfinite_band_isometry_bound
      (fun Z : Lp ℝ (2 : ℝ≥0∞) P => ∫ ω, Z ω ∂P)
      (AvramDividend.Classical.avram_wave4_p1_probability_l2_expectation_continuous_original_space P)
      hcentered
