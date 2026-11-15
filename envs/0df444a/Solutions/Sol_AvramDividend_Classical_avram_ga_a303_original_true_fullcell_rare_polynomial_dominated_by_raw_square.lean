-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a303_original_true_fullcell_rare_polynomial_dominated_by_raw_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:45:56.798521+00:00
-- url     : https://prove2.me/submissions/ee5bb462-657c-4ec0-ac2c-69e63895ea26

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a223_original_physical_gaussian_drift_below_half_tail_threshold_eventually
import Theorems.Thm_AvramDividend_Classical_avram_ga_a261_large_increment_small_drift_raw_square_dominates_source_polynomial
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (ρ : Ω → ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω-X.X (s m i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      R m i ω - (Δ m : ℝ) * X.c
    ∀ᶠ m : ℕ in atTop, ∀ ω : Ω,
      (∑ i ∈ Finset.range m,
        if (s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω) ∧
           δ ≤ |R m i ω| then
          1 + |R m i ω| + (Z m i ω)^2 / 2 else 0) ≤
      (1/δ^2 + 1/δ + 2) *
      (∑ i ∈ Finset.range m,
        if s m i < ρ ω then
          (if δ ≤ |R m i ω| then (R m i ω)^2 else 0)
        else 0) := by
  intro Δ s R Z
  have hd := avram_ga_a223_original_physical_gaussian_drift_below_half_tail_threshold_eventually
    n X.c δ hδ
  filter_upwards [hd] with m hm
  intro ω
  have hDrift : |(Δ m : ℝ) * X.c| ≤ δ := by
    dsimp [Δ] at hm ⊢
    linarith
  have hC : 0 ≤ (1/δ^2 + 1/δ + 2 : ℝ) := by positivity
  calc
    (∑ i ∈ Finset.range m,
      if (s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω) ∧
          δ ≤ |R m i ω| then
        1 + |R m i ω| + (Z m i ω)^2/2 else 0) ≤
      ∑ i ∈ Finset.range m,
        (1/δ^2+1/δ+2) *
        (if s m i < ρ ω then
          (if δ ≤ |R m i ω| then (R m i ω)^2 else 0)
        else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hb : (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧
          δ ≤ |R m i ω|
      · have hP := avram_ga_a261_large_increment_small_drift_raw_square_dominates_source_polynomial
          δ (R m i ω) (Z m i ω) ((Δ m : ℝ)*X.c)
          hδ hb.2 hDrift rfl
        simpa [hb, hb.1.1, hb.2] using hP
      · have hRight : 0 ≤ (1/δ^2+1/δ+2) *
          (if s m i < ρ ω then
            (if δ ≤ |R m i ω| then (R m i ω)^2 else 0)
          else 0) := by
          apply mul_nonneg hC
          split_ifs <;> positivity
        simpa [hb] using hRight
    _ = (1/δ^2+1/δ+2) *
        (∑ i ∈ Finset.range m,
          if s m i < ρ ω then
            (if δ ≤ |R m i ω| then (R m i ω)^2 else 0)
          else 0) := by
      rw [Finset.mul_sum]
