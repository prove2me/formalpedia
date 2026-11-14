-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a195_original_physical_full_raw_square_pointwise_le_prefix_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:51:59.079354+00:00
-- url     : https://prove2.me/submissions/c0e938cc-3ee2-4f12-ba46-dbb23352c484

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a57_true_stop_raw_quadratic_energy_finset_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original physically full Gaussian raw-square grid energy is pointwise
dominated by twice original stopped-prefix centred energy and drift budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Z : ℕ → ℝ := fun i =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    (∑ i ∈ Finset.range m,
        if s i < ρ ω ∧ s i + Δ ≤ ρ ω then
          (Z i + (Δ : ℝ) * X.c)^2 else 0) ≤
      2 * (∑ i ∈ Finset.range m,
        if s i < ρ ω then (Z i)^2 else 0) +
      2 * (m : ℝ) * ((Δ : ℝ) * X.c)^2 := by
  classical
  intro Δ s Z
  have hRaw := avram_ga_a57_true_stop_raw_quadratic_energy_finset_bound
    (Finset.range m) Z
    (fun i => s i < ρ ω ∧ s i + Δ ≤ ρ ω) ((Δ : ℝ) * X.c)
  calc
    (∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω then
        (Z i + (Δ : ℝ) * X.c)^2 else 0) ≤
      2 * (∑ i ∈ Finset.range m,
        if s i < ρ ω ∧ s i + Δ ≤ ρ ω then (Z i)^2 else 0) +
      2 * (Finset.range m).card * ((Δ : ℝ) * X.c)^2 := hRaw
    _ ≤ 2 * (∑ i ∈ Finset.range m,
        if s i < ρ ω then (Z i)^2 else 0) +
      2 * (m : ℝ) * ((Δ : ℝ) * X.c)^2 := by
      simp only [Finset.card_range]
      gcongr
      by_cases hf : s i < ρ ω ∧ s i + Δ ≤ ρ ω
      · simp [hf, hf.1]
      · by_cases hp : s i < ρ ω
        · simp only [if_neg hf,if_pos hp]
          positivity
        · simp only [if_neg hf,if_neg hp]
          exact le_refl (0 : ℝ)
