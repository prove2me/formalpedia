-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_finite_band_centered_l2_limit_preserves_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:45:56.590079+00:00
-- url     : https://prove2.me/submissions/09769062-3283-4c96-8a83-6e7de0b90083

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_band_l2_increment_bound_yields_complete_stopped_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem solution
    {α W : Type*} [MeasurableSpace α]
    [MetricSpace W] [CompleteSpace W]
    (μ : Measure α)
    (f : α → ℝ) (hf : Measurable f)
    (henergy : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ < ∞)
    (B : ℕ → Set α) (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, μ (B n) < ∞)
    (hBmono : Monotone B) (hBcover : (⋃ n, B n) = Set.univ)
    (M : ℕ → W)
    (hfinite_band_isometry_bound :
      ∀ m n, m ≤ n →
        dist (M m) (M n) ≤
          (eLpNorm ((B m)ᶜ.indicator f) (2 : ℝ≥0∞) μ).toReal)
    (φ : W → ℝ) (hφ : Continuous φ)
    (hcentered : ∀ n, φ (M n) = 0) :
    ∃ Mlimit : W,
      Tendsto M Filter.atTop (nhds Mlimit) ∧ φ Mlimit = 0 := by
  obtain ⟨Mlimit, hlim⟩ :=
    AvramDividend.Classical.avram_wave4_p1_finite_band_l2_increment_bound_yields_complete_stopped_limit
      μ f hf henergy B hB hBfinite hBmono hBcover M hfinite_band_isometry_bound
  refine ⟨Mlimit, hlim, ?_⟩
  have hφlim : Tendsto (fun n : ℕ => φ (M n))
      Filter.atTop (nhds (φ Mlimit)) :=
    (hφ.tendsto Mlimit).comp hlim
  have hφzero : Tendsto (fun n : ℕ => φ (M n))
      Filter.atTop (nhds (0 : ℝ)) := by
    have heq : (fun n : ℕ => φ (M n)) = (fun _ : ℕ => (0 : ℝ)) := by
      funext n
      exact hcentered n
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hφlim hφzero
