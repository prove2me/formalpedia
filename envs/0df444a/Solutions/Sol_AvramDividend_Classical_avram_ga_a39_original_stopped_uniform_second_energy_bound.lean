-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a39_original_stopped_uniform_second_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:37:25.31342+00:00
-- url     : https://prove2.me/submissions/24686a59-063f-484e-947b-98ec2278fd2a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a37_original_stopped_grid_second_energy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a38_original_grid_second_energy_uniform_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

-- Uniform original Gaussian expected quadratic-energy budget under the actual stopping mask.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (Δ : ℕ → ℝ≥0)
    (hΔ : ∀ m, (Δ m : ℝ) = (n : ℝ) / ((m : ℝ) + 1))
    (ρ : Ω → ℝ≥0)
    (hMeas : ∀ (m : ℕ) (i : ℕ), i ∈ Finset.range m →
      Measurable (fun ω : Ω =>
        X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
          X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c)) :
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c
    ∀ m : ℕ,
      (∫⁻ ω, ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ m < ρ ω then
          ENNReal.ofReal ((Z m i ω) ^ 2) else 0 ∂P) ≤
        ENNReal.ofReal ((n : ℝ) * X.σ ^ 2) := by
  classical
  dsimp
  intro m
  let Z : ℕ → Ω → ℝ := fun i ω =>
    X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
      X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c
  change (∫⁻ ω, ∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * Δ m < ρ ω then
        ENNReal.ofReal ((Z i ω) ^ 2) else 0 ∂P) ≤
      ENNReal.ofReal ((n : ℝ) * X.σ ^ 2)
  have hSource :
      (∫⁻ ω, ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ m < ρ ω then
          ENNReal.ofReal ((Z i ω) ^ 2) else 0 ∂P) ≤
      ∑ _i ∈ Finset.range m, ENNReal.ofReal ((Δ m : ℝ) * X.σ ^ 2) := by
    exact avram_ga_a37_original_stopped_grid_second_energy X hν
      (Finset.range m) (fun i => (i : ℝ≥0) * Δ m) (Δ m) ρ (hMeas m)
  have hVarNonneg : 0 ≤ (Δ m : ℝ) * X.σ ^ 2 := by positivity
  have hSum :
      (∑ _i ∈ Finset.range m,
        ENNReal.ofReal ((Δ m : ℝ) * X.σ ^ 2)) =
        ENNReal.ofReal (∑ _i ∈ Finset.range m,
          ((Δ m : ℝ) * X.σ ^ 2)) := by
    symm
    exact ENNReal.ofReal_sum_of_nonneg (fun _i _hi => hVarNonneg)
  calc
    (∫⁻ ω, ∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * Δ m < ρ ω then
        ENNReal.ofReal ((Z i ω) ^ 2) else 0 ∂P) ≤
      ∑ _i ∈ Finset.range m, ENNReal.ofReal ((Δ m : ℝ) * X.σ ^ 2) :=
        hSource
    _ = ENNReal.ofReal (∑ _i ∈ Finset.range m,
        ((Δ m : ℝ) * X.σ ^ 2)) := hSum
    _ ≤ ENNReal.ofReal ((n : ℝ) * X.σ ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hΔ m]
        using avram_ga_a38_original_grid_second_energy_uniform_rate n m X.σ
