-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a229_original_gaussian_true_physical_mesh_raw_and_centered_positive_exp_sums_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:07:11.163437+00:00
-- url     : https://prove2.me/submissions/ea3da7e9-1759-4a77-a502-0239bb06181c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a227_original_gaussian_normalised_positive_exponential_tail_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a228_original_raw_gaussian_positive_exponential_increment_tail_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (θ δ : ℝ) (hθ : 0 ≤ θ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω - X.X (s m i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      (R m i ω - (Δ m : ℝ) * X.c) / X.σ
    (∀ m, Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if δ ≤ R m i ω then Real.exp (θ * R m i ω) else 0) P) ∧
    (∀ m, Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if δ / (2 * X.σ) ≤ Z m i ω
        then Real.exp ((θ * X.σ) * Z m i ω) else 0) P) := by
  intro Δ s R Z
  constructor
  · intro m
    apply integrable_finset_sum
    intro i hi
    have hst : s m i ≤ s m i + Δ m :=
      le_add_of_nonneg_right (by positivity)
    exact avram_ga_a228_original_raw_gaussian_positive_exponential_increment_tail_integrable
      X hν hσ (s m i) (s m i + Δ m) hst θ δ hθ
  · intro m
    apply integrable_finset_sum
    intro i hi
    have hst : s m i ≤ s m i + Δ m :=
      le_add_of_nonneg_right (by positivity)
    have hθ' : 0 ≤ θ * X.σ := mul_nonneg hθ hσ.le
    have hz := avram_ga_a227_original_gaussian_normalised_positive_exponential_tail_integrable
      X hν hσ (s m i) (s m i + Δ m) hst
      (θ * X.σ) (δ / (2 * X.σ)) hθ'
    simpa only [Z,R,add_tsub_cancel_left] using hz
