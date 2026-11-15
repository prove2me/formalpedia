-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a225_original_raw_positive_gaussian_exp_tail_fullmesh_eventual_centered_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:56:53.558945+00:00
-- url     : https://prove2.me/submissions/08aa6327-7ba3-453f-8252-9b4a22ef0fc4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a222_raw_positive_Gaussian_exponential_tail_dominated_by_centered_normalised
import Theorems.Thm_AvramDividend_Classical_avram_ga_a223_original_physical_gaussian_drift_below_half_tail_threshold_eventually
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
    (hσ : 0 < X.σ) (n : ℕ) (θ δ : ℝ)
    (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω - X.X (s m i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      (R m i ω - (Δ m : ℝ) * X.c) / X.σ
    ∀ᶠ m : ℕ in atTop, ∀ ω : Ω,
      (∑ i ∈ Finset.range m,
        if δ ≤ R m i ω then Real.exp (θ * R m i ω) else 0) ≤
      Real.exp (θ * δ / 2) *
      (∑ i ∈ Finset.range m,
        if δ / (2 * X.σ) ≤ Z m i ω
        then Real.exp ((θ * X.σ) * Z m i ω) else 0) := by
  intro Δ s R Z
  have hd := avram_ga_a223_original_physical_gaussian_drift_below_half_tail_threshold_eventually
    n X.c δ hδ
  filter_upwards [hd] with m hm
  intro ω
  have hDrift : |(Δ m : ℝ) * X.c| ≤ δ / 2 := hm
  have hLine (i : ℕ) :
      (if δ ≤ R m i ω then Real.exp (θ * R m i ω) else 0) ≤
      Real.exp (θ * |(Δ m : ℝ) * X.c|) *
        (if δ / (2 * X.σ) ≤ Z m i ω
         then Real.exp ((θ * X.σ) * Z m i ω) else 0) := by
    exact avram_ga_a222_raw_positive_Gaussian_exponential_tail_dominated_by_centered_normalised
      θ δ X.σ ((Δ m : ℝ) * X.c) (R m i ω) hθ hδ hσ hDrift
  have hS : 0 ≤ ∑ i ∈ Finset.range m,
        (if δ / (2 * X.σ) ≤ Z m i ω
        then Real.exp ((θ * X.σ) * Z m i ω) else 0) := by
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  calc
    (∑ i ∈ Finset.range m,
      if δ ≤ R m i ω then Real.exp (θ * R m i ω) else 0) ≤
      ∑ i ∈ Finset.range m,
        (Real.exp (θ * |(Δ m : ℝ) * X.c|) *
          (if δ / (2 * X.σ) ≤ Z m i ω
          then Real.exp ((θ * X.σ) * Z m i ω) else 0)) := by
        exact Finset.sum_le_sum (fun i hi => hLine i)
    _ = Real.exp (θ * |(Δ m : ℝ) * X.c|) *
        ∑ i ∈ Finset.range m,
          (if δ / (2 * X.σ) ≤ Z m i ω
          then Real.exp ((θ * X.σ) * Z m i ω) else 0) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (θ * δ / 2) *
        ∑ i ∈ Finset.range m,
          (if δ / (2 * X.σ) ≤ Z m i ω
          then Real.exp ((θ * X.σ) * Z m i ω) else 0) := by
        apply mul_le_mul_of_nonneg_right _ hS
        apply Real.exp_le_exp.mpr
        have htmp := mul_nonneg hθ (sub_nonneg.mpr hDrift)
        nlinarith
