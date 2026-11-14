-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a123_b0_original_root_exact_genuine_full_cross_residual_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:11:13.143928+00:00
-- url     : https://prove2.me/submissions/a2274ac8-027c-4e25-a484-1a018ad16676

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a121_b0_root_spatial_residual_eq_genuine_clipped_cell_sum
import Theorems.Thm_AvramDividend_Classical_avram_ga_a94_original_gaussian_clipped_spatial_residual_true_full_cross_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The original three-sum Gaussian positive-interior spatial residual equals the genuine full-cell and stop-straddling crossing-cell source residuals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun i => min (s i) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i =>
      E (s i) * (deriv w (Y (s i)) * Z i +
        (iteratedDeriv 2 w (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) +
        (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
    let U : ℕ → ℝ := fun i =>
      E (v (i + 1)) *
        (w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
          w (Y (v i))) -
      (if s i < ρ then H i else 0)
    let A : ℕ → ℝ := fun i =>
      E (v (i + 1)) * (w (x + X.X (v (i + 1)) ω -
        rightLimit D (v i) ω) - w (Y (v i)))
    let B : ℕ → ℝ := fun i =>
      if s i < ρ then E (s i) * (deriv w (Y (s i)) * Z i +
        (iteratedDeriv 2 w (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) else 0
    let G : ℕ → ℝ := fun i =>
      if s i < ρ then (Δ : ℝ) * E (s i) *
        X.generator w (Y (s i)) else 0
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i
    let C : ℕ → ℝ := fun i =>
      E ρ * (w (Y (s i) + (X.X ρ ω - X.X (s i) ω)) -
        w (Y (s i))) - H i
    (∑ i ∈ Finset.range m, A i) -
      (∑ i ∈ Finset.range m, B i) -
      (∑ i ∈ Finset.range m, G i) =
      (∑ i ∈ Finset.range m,
        if s i < ρ ∧ s i + Δ ≤ ρ then F i else 0) +
      (∑ i ∈ Finset.range m,
        if s i < ρ ∧ ρ < s i + Δ then C i else 0) := by
  have hRoot := avram_ga_a121_b0_root_spatial_residual_eq_genuine_clipped_cell_sum
    X x D w q ω n m ρ
  have hPartition :=
    avram_ga_a94_original_gaussian_clipped_spatial_residual_true_full_cross_partition
      X x D w q ω n m ρ
  exact hRoot.trans hPartition
