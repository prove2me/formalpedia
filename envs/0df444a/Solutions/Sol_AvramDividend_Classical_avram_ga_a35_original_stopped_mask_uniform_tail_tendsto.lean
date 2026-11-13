-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a35_original_stopped_mask_uniform_tail_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:06:47.952847+00:00
-- url     : https://prove2.me/submissions/4d566625-2b81-465c-b74a-579f339af3d8

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a33_original_uniform_grid_large_tail_L1_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

-- True pre-stop physical-grid source large-increment energy vanishes in expectation.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (Δ : ℕ → ℝ≥0)
    (hΔ : ∀ m, (Δ m : ℝ) = (n : ℝ) / ((m : ℝ) + 1))
    (hMeas : ∀ (m : ℕ) (i : ℕ), i ∈ Finset.range m →
      Measurable (fun ω : Ω =>
        (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
          X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) / X.σ))
    (ρ : Ω → ℝ≥0) (r : ℝ) (hr : 0 < r) :
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) / X.σ
    Tendsto (fun m : ℕ =>
      ∫⁻ ω, ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ m < ρ ω then
          ENNReal.ofReal (if r ≤ |Z m i ω| then (Z m i ω) ^ 2 else 0)
        else 0 ∂P) atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  dsimp
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
      X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) / X.σ
  change Tendsto (fun m : ℕ =>
    ∫⁻ ω, ∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * Δ m < ρ ω then
        ENNReal.ofReal (if r ≤ |Z m i ω| then (Z m i ω) ^ 2 else 0)
      else 0 ∂P) atTop (𝓝 (0 : ℝ≥0∞))
  have hSource : Tendsto (fun m : ℕ =>
      ∫⁻ ω, ∑ i ∈ Finset.range m,
        ENNReal.ofReal (if r ≤ |Z m i ω| then (Z m i ω) ^ 2 else 0) ∂P)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    exact avram_ga_a33_original_uniform_grid_large_tail_L1_tendsto
      X hν hσ n Δ hΔ hMeas r hr
  have hBound (m : ℕ) :
      (∫⁻ ω, ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ m < ρ ω then
          ENNReal.ofReal (if r ≤ |Z m i ω| then (Z m i ω) ^ 2 else 0)
        else 0 ∂P) ≤
      (∫⁻ ω, ∑ i ∈ Finset.range m,
        ENNReal.ofReal (if r ≤ |Z m i ω| then (Z m i ω) ^ 2 else 0) ∂P) := by
    apply lintegral_mono
    intro ω
    apply Finset.sum_le_sum
    intro i hi
    by_cases h : (i : ℝ≥0) * Δ m < ρ ω
    · simp only [if_pos h, le_refl]
    · simp only [if_neg h]
      exact zero_le
  apply Filter.Tendsto.squeeze
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)) hSource
  · intro m; exact zero_le
  · intro m; exact hBound m
