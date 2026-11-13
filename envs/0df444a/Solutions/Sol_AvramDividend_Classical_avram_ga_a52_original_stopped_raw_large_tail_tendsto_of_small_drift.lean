-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a52_original_stopped_raw_large_tail_tendsto_of_small_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:29:34.375916+00:00
-- url     : https://prove2.me/submissions/8da5c0d0-2eb3-4977-8be4-c0c361c98021

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a41_original_stopped_unnormalised_large_tail_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_ga_a51_stopped_raw_tail_energy_lintegral_le_centered
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original stopped raw Gaussian source large-increment energy tends to zero from centred Lindeberg. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (Δ : ℕ → ℝ≥0)
    (hΔ : ∀ m, (Δ m : ℝ) = (n : ℝ) / ((m : ℝ) + 1))
    (hMeas : ∀ (m : ℕ) (i : ℕ), i ∈ Finset.range m →
      Measurable (fun ω : Ω => (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) / X.σ))
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ)
    (η : ℝ) (hη : 0 < η)
    (hDrift : ∀ᶠ m in atTop, |(Δ m : ℝ) * X.c| ≤ η / 2)
    (hSumMeas : ∀ m : ℕ, Measurable (fun ω : Ω =>
      ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ m < ρ ω then
          ENNReal.ofReal (if η / 2 ≤
            |X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
              X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c| then
            (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
              X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) ^ 2 else 0)
        else 0)) :
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
  dsimp
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
      X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c
  let Cent : ℕ → ℝ≥0∞ := fun m => ∫⁻ ω, ∑ i ∈ Finset.range m,
    if (i : ℝ≥0) * Δ m < ρ ω then
      ENNReal.ofReal (if η / 2 ≤ |Z m i ω| then (Z m i ω)^2 else 0)
    else 0 ∂P
  let Raw : ℕ → ℝ≥0∞ := fun m => ∫⁻ ω, ∑ i ∈ Finset.range m,
    if (i : ℝ≥0) * Δ m < ρ ω then
      ENNReal.ofReal (if η ≤ |Z m i ω + (Δ m : ℝ) * X.c| then
        (Z m i ω + (Δ m : ℝ) * X.c)^2 else 0)
    else 0 ∂P
  change Tendsto Raw atTop (𝓝 (0 : ℝ≥0∞))
  have hHalf : 0 < η / 2 := by linarith
  have hCent : Tendsto Cent atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [Cent, Z] using
      (avram_ga_a41_original_stopped_unnormalised_large_tail_tendsto
        X hν hσ n Δ hΔ hMeas ρ hρ (η / 2) hHalf)
  have hUpper : Tendsto (fun m => (4 : ℝ≥0∞) * Cent m)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hc : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have hh := ENNReal.Tendsto.const_mul hCent (Or.inr hc)
    simpa only [mul_zero] using hh
  have hBound : ∀ᶠ m in atTop, Raw m ≤ (4 : ℝ≥0∞) * Cent m := by
    filter_upwards [hDrift] with m hm
    exact avram_ga_a51_stopped_raw_tail_energy_lintegral_le_centered
      P m (fun i => (i : ℝ≥0) * Δ m) ρ (Z m)
      ((Δ m : ℝ) * X.c) η hη hm (hSumMeas m)
  have hLower : ∀ᶠ m in atTop, (0 : ℝ≥0∞) ≤ Raw m :=
    Eventually.of_forall (fun m => zero_le)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hUpper hLower hBound
