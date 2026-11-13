-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a41_original_stopped_unnormalised_large_tail_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:41:44.486581+00:00
-- url     : https://prove2.me/submissions/f83cb8d3-1a27-47f2-a913-9087a1d3349b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a35_original_stopped_mask_uniform_tail_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_ga_a40_physical_normalised_large_tail_scaling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

-- Genuine unnormalised Gaussian source large-cell quadratic energy tends to zero.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (Δ : ℕ → ℝ≥0)
    (hΔ : ∀ m, (Δ m : ℝ) = (n : ℝ) / ((m : ℝ) + 1))
    (hMeas : ∀ (m : ℕ) (i : ℕ), i ∈ Finset.range m →
      Measurable (fun ω : Ω => (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) / X.σ))
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ) (η : ℝ) (hη : 0 < η) :
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c
    Tendsto (fun m : ℕ => ∫⁻ ω, ∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * Δ m < ρ ω then
        ENNReal.ofReal (if η ≤ |Z m i ω| then (Z m i ω) ^ 2 else 0)
      else 0 ∂P) atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  dsimp
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
      X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c
  let N : ℕ → ℕ → Ω → ℝ := fun m i ω => Z m i ω / X.σ
  change Tendsto (fun m : ℕ => ∫⁻ ω, ∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * Δ m < ρ ω then
        ENNReal.ofReal (if η ≤ |Z m i ω| then (Z m i ω) ^ 2 else 0)
      else 0 ∂P) atTop (𝓝 (0 : ℝ≥0∞))
  have hr : 0 < η / X.σ := div_pos hη hσ
  have hNorm : Tendsto (fun m : ℕ => ∫⁻ ω, ∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * Δ m < ρ ω then
        ENNReal.ofReal (if η / X.σ ≤ |N m i ω| then (N m i ω) ^ 2 else 0)
      else 0 ∂P) atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [N, Z] using
      (avram_ga_a35_original_stopped_mask_uniform_tail_tendsto
        X hν hσ n Δ hΔ hMeas ρ (η / X.σ) hr)
  have hM (m : ℕ) : Measurable (fun ω : Ω =>
      ∑ i ∈ Finset.range m, if (i : ℝ≥0) * Δ m < ρ ω then
        ENNReal.ofReal (if η / X.σ ≤ |N m i ω| then (N m i ω) ^ 2 else 0)
      else 0) := by
    apply Finset.measurable_sum
    intro i hi
    have hNi : Measurable (N m i) := hMeas m i hi
    have hSet : MeasurableSet {ω : Ω | η / X.σ ≤ |N m i ω|} :=
      measurableSet_le measurable_const hNi.abs
    have hReal : Measurable (fun ω : Ω =>
        if η / X.σ ≤ |N m i ω| then (N m i ω) ^ 2 else 0) :=
      Measurable.ite hSet (hNi.pow_const 2) measurable_const
    have hTail : Measurable (fun ω : Ω =>
        ENNReal.ofReal (if η / X.σ ≤ |N m i ω| then
          (N m i ω) ^ 2 else 0)) :=
      ENNReal.measurable_ofReal.comp hReal
    exact Measurable.ite (measurableSet_lt measurable_const hρ) hTail measurable_const
  have hPoint (m : ℕ) (ω : Ω) :
      (∑ i ∈ Finset.range m, if (i : ℝ≥0) * Δ m < ρ ω then
        ENNReal.ofReal (if η ≤ |Z m i ω| then (Z m i ω) ^ 2 else 0)
      else 0) =
      ENNReal.ofReal (X.σ ^ 2) * (∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ m < ρ ω then
          ENNReal.ofReal (if η / X.σ ≤ |N m i ω| then
            (N m i ω) ^ 2 else 0) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : (i : ℝ≥0) * Δ m < ρ ω
    · simp only [if_pos h]
      change ENNReal.ofReal (if η ≤ |Z m i ω| then (Z m i ω)^2 else 0) =
        ENNReal.ofReal (X.σ^2) *
          ENNReal.ofReal (if η / X.σ ≤ |Z m i ω / X.σ| then
            (Z m i ω / X.σ)^2 else 0)
      rw [← ENNReal.ofReal_mul (sq_nonneg X.σ)]
      exact congrArg ENNReal.ofReal
        (avram_ga_a40_physical_normalised_large_tail_scaling (Z m i ω) X.σ η hσ hη)
    · simp only [if_neg h, mul_zero]
  have hInt (m : ℕ) :
      (∫⁻ ω, ∑ i ∈ Finset.range m, if (i : ℝ≥0) * Δ m < ρ ω then
        ENNReal.ofReal (if η ≤ |Z m i ω| then (Z m i ω)^2 else 0)
      else 0 ∂P) =
      ENNReal.ofReal (X.σ^2) *
        (∫⁻ ω, ∑ i ∈ Finset.range m, if (i : ℝ≥0) * Δ m < ρ ω then
          ENNReal.ofReal (if η / X.σ ≤ |N m i ω| then
            (N m i ω)^2 else 0) else 0 ∂P) := by
    simp_rw [hPoint m]
    exact lintegral_const_mul _ (hM m)
  have hConst : ENNReal.ofReal (X.σ^2) ≠ ⊤ := by simp
  have hLim := ENNReal.Tendsto.const_mul hNorm (Or.inr hConst)
  simpa only [hInt, mul_zero] using hLim
