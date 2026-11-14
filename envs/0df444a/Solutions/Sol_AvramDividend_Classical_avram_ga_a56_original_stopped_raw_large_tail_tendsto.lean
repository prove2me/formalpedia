-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a56_original_stopped_raw_large_tail_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:16:19.252335+00:00
-- url     : https://prove2.me/submissions/a3027d54-86dd-49ec-8c5c-50abc46999e8

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a52_original_stopped_raw_large_tail_tendsto_of_small_drift
import Theorems.Thm_AvramDividend_Classical_avram_ga_a53_original_uniform_mesh_drift_eventually_small
import Theorems.Thm_AvramDividend_Classical_avram_ga_a55_true_stop_large_tail_measurable_from_normalised_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- On the genuine original zero-jump source, stopped raw Gaussian large-cell L1 energy vanishes without extra measurability or drift assumptions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (Δ : ℕ → ℝ≥0)
    (hΔ : ∀ m, (Δ m : ℝ) = (n : ℝ) / ((m : ℝ) + 1))
    (hMeas : ∀ (m : ℕ) (i : ℕ), i ∈ Finset.range m →
      Measurable (fun ω : Ω => (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) / X.σ))
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ)
    (η : ℝ) (hη : 0 < η) :
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c
    Tendsto (fun m : ℕ => ∫⁻ ω, ∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * Δ m < ρ ω then
        ENNReal.ofReal (if η ≤
          |Z m i ω + (Δ m : ℝ) * X.c| then
          (Z m i ω + (Δ m : ℝ) * X.c) ^ 2 else 0)
      else 0 ∂P) atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
      X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c
  have hσne : X.σ ≠ 0 := ne_of_gt hσ
  have hDrift : ∀ᶠ m in atTop, |(Δ m : ℝ) * X.c| ≤ η / 2 := by
    have hh :=
      avram_ga_a53_original_uniform_mesh_drift_eventually_small n X.c η hη
    dsimp at hh
    filter_upwards [hh] with m hm
    have hCast : (((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) =
        (n : ℝ) / ((m : ℝ) + 1) := by
      norm_num
    calc
      |(Δ m : ℝ) * X.c| = |((n : ℝ) / ((m : ℝ) + 1)) * X.c| := by
        rw [hΔ m]
      _ = |((((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) * X.c)| := by
        rw [hCast]
      _ ≤ η / 2 := hm
  have hSumMeas (m : ℕ) : Measurable (fun ω : Ω =>
      ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ m < ρ ω then
          ENNReal.ofReal (if η / 2 ≤ |Z m i ω| then
            (Z m i ω)^2 else 0) else 0) := by
    apply avram_ga_a55_true_stop_large_tail_measurable_from_normalised_source
      (Finset.range m) (fun i => (i : ℝ≥0) * Δ m)
      ρ hρ (Z m) X.σ hσne
    intro i hi
    simpa only [Z] using hMeas m i hi
  simpa only [Z] using
    (avram_ga_a52_original_stopped_raw_large_tail_tendsto_of_small_drift
      X hν hσ n Δ hΔ hMeas ρ hρ η hη hDrift
      (by
        intro m
        simpa only [Z] using hSumMeas m))
