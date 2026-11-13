-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a34_original_stopped_mask_large_tail_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:06:28.532872+00:00
-- url     : https://prove2.me/submissions/d084a893-245b-4982-b9b9-1b3b88ce55c7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a31_original_physical_grid_lindeberg_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

-- Positive stopped clock masks preserve the original grid Lindeberg tail bound.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (hσ : 0 < X.σ)
    (S : Finset ℕ) (s : ℕ → ℝ≥0) (Δ : ℝ≥0)
    (ρ : Ω → ℝ≥0)
    (hMeas : ∀ i ∈ S, Measurable (fun ω : Ω =>
      (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c) / X.σ))
    (r : ℝ) (hr : 0 < r) :
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c) / X.σ
    (∫⁻ ω, ∑ i ∈ S,
      if s i < ρ ω then
        ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0)
      else 0 ∂P) ≤
      ENNReal.ofReal (1 / r ^ 2) *
        (∑ _i ∈ S, ENNReal.ofReal (3 * (Δ : ℝ) ^ 2)) := by
  dsimp
  let Z : ℕ → Ω → ℝ := fun i ω =>
    (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c) / X.σ
  change (∫⁻ ω, ∑ i ∈ S,
      if s i < ρ ω then
        ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0)
      else 0 ∂P) ≤
      ENNReal.ofReal (1 / r ^ 2) *
        (∑ _i ∈ S, ENNReal.ofReal (3 * (Δ : ℝ) ^ 2))
  have hPoint (ω : Ω) :
      (∑ i ∈ S, if s i < ρ ω then
        ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0)
      else 0) ≤
      (∑ i ∈ S,
        ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0)) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases h : s i < ρ ω
    · simp only [if_pos h, le_refl]
    · simp only [if_neg h]
      exact zero_le
  calc
    (∫⁻ ω, ∑ i ∈ S,
      if s i < ρ ω then
        ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0)
      else 0 ∂P) ≤
      (∫⁻ ω, ∑ i ∈ S,
        ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0) ∂P) :=
          lintegral_mono hPoint
    _ ≤ ENNReal.ofReal (1 / r ^ 2) *
        (∑ _i ∈ S, ENNReal.ofReal (3 * (Δ : ℝ) ^ 2)) := by
          exact avram_ga_a31_original_physical_grid_lindeberg_energy
            X hν hσ S s Δ hMeas r hr
