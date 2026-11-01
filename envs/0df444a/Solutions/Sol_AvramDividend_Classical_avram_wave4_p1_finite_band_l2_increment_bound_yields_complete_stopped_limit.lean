-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_finite_band_l2_increment_bound_yields_complete_stopped_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:35:41.403075+00:00
-- url     : https://prove2.me/submissions/1e553224-43f3-40c3-b088-bf5d47ba91db

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_finite_l2_band_cutoff_converges

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
          (eLpNorm ((B m)ᶜ.indicator f) (2 : ℝ≥0∞) μ).toReal) :
    ∃ Mlimit : W, Tendsto M Filter.atTop (nhds Mlimit) := by
  have hcut :
      Tendsto (fun n : ℕ =>
        eLpNorm ((B n)ᶜ.indicator f) (2 : ℝ≥0∞) μ)
        Filter.atTop (nhds (0 : ℝ≥0∞)) :=
    AvramDividend.Classical.avram_wave4_p1_sigma_finite_l2_band_cutoff_converges
      μ f hf henergy B hB hBfinite hBmono hBcover
  have htail :
      Tendsto (fun n : ℕ =>
        (eLpNorm ((B n)ᶜ.indicator f) (2 : ℝ≥0∞) μ).toReal)
        Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto.comp hcut
  have hCauchy : CauchySeq M :=
    cauchySeq_of_le_tendsto_0'
      (fun n : ℕ =>
        (eLpNorm ((B n)ᶜ.indicator f) (2 : ℝ≥0∞) μ).toReal)
      hfinite_band_isometry_bound htail
  exact cauchySeq_tendsto_of_complete hCauchy
