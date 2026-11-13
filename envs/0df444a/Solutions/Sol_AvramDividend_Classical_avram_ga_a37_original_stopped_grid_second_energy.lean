-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a37_original_stopped_grid_second_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:19:00.643248+00:00
-- url     : https://prove2.me/submissions/0f5e0633-7a19-46f5-92f3-2c53b5400c03

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a36_original_grid_second_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

-- Restricting original physical Gaussian quadratic energy to pre-stop cells preserves the variance bound.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ℕ) (s : ℕ → ℝ≥0) (Δ : ℝ≥0)
    (ρ : Ω → ℝ≥0)
    (hMeas : ∀ i ∈ S, Measurable (fun ω : Ω =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c)) :
    let Z : ℕ → Ω → ℝ := fun i ω =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    (∫⁻ ω, ∑ i ∈ S,
      if s i < ρ ω then ENNReal.ofReal ((Z i ω) ^ 2) else 0 ∂P) ≤
      ∑ _i ∈ S, ENNReal.ofReal ((Δ : ℝ) * X.σ ^ 2) := by
  classical
  dsimp
  let Z : ℕ → Ω → ℝ := fun i ω =>
    X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
  change (∫⁻ ω, ∑ i ∈ S,
      if s i < ρ ω then ENNReal.ofReal ((Z i ω) ^ 2) else 0 ∂P) ≤
      ∑ _i ∈ S, ENNReal.ofReal ((Δ : ℝ) * X.σ ^ 2)
  have hPoint (ω : Ω) :
      (∑ i ∈ S,
        if s i < ρ ω then ENNReal.ofReal ((Z i ω) ^ 2) else 0) ≤
      (∑ i ∈ S, ENNReal.ofReal ((Z i ω) ^ 2)) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases h : s i < ρ ω
    · simp only [if_pos h, le_refl]
    · simp only [if_neg h]
      exact zero_le
  calc
    (∫⁻ ω, ∑ i ∈ S,
      if s i < ρ ω then ENNReal.ofReal ((Z i ω) ^ 2) else 0 ∂P) ≤
      (∫⁻ ω, ∑ i ∈ S, ENNReal.ofReal ((Z i ω) ^ 2) ∂P) :=
        lintegral_mono hPoint
    _ ≤ ∑ _i ∈ S, ENNReal.ofReal ((Δ : ℝ) * X.σ ^ 2) := by
          exact avram_ga_a36_original_grid_second_energy X hν S s Δ hMeas
