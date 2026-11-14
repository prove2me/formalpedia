-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a87_original_clipped_spatial_source_residual_fullcell_error_algebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:19.829747+00:00
-- url     : https://prove2.me/submissions/a0db07ea-e38f-45a3-8f0f-4d1fe7d90ae9

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original clipped stopped Gaussian spatial residual is exactly a full-source Gaussian compensated residual plus a clipping/discount error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ρ : Ω → ℝ≥0) (ω : Ω) (n m : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun i => min (s i) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let A : ℕ → ℝ := fun i =>
      E (v (i + 1)) *
        (w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
          w (Y (v i)))
    let B : ℕ → ℝ := fun i =>
      if s i < ρ ω then E (s i) * (w (Y (s i) + R i) - w (Y (s i)))
      else 0
    let C : ℕ → ℝ := fun i =>
      if s i < ρ ω then E (s i) *
        (deriv w (Y (s i)) * Z i +
          (iteratedDeriv 2 w (Y (s i)) / 2) *
            (Z i^2 - (Δ : ℝ) * X.σ^2)) else 0
    let G : ℕ → ℝ := fun i =>
      if s i < ρ ω then
        (Δ : ℝ) * E (s i) * X.generator w (Y (s i)) else 0
    (∑ i ∈ Finset.range m, A i) -
      (∑ i ∈ Finset.range m, C i) -
      (∑ i ∈ Finset.range m, G i) =
      (∑ i ∈ Finset.range m, (B i - C i - G i)) +
      (∑ i ∈ Finset.range m, (A i - B i)) := by
  classical
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let v : ℕ → ℝ≥0 := fun i => min (s i) (ρ ω)
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let Y : ℝ≥0 → ℝ := fun t =>
    x + X.X t ω - rightLimit D t ω
  let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
  let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
  let A : ℕ → ℝ := fun i =>
    E (v (i + 1)) *
      (w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
        w (Y (v i)))
  let B : ℕ → ℝ := fun i =>
    if s i < ρ ω then E (s i) * (w (Y (s i) + R i) - w (Y (s i)))
    else 0
  let C : ℕ → ℝ := fun i =>
    if s i < ρ ω then E (s i) *
      (deriv w (Y (s i)) * Z i +
        (iteratedDeriv 2 w (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) else 0
  let G : ℕ → ℝ := fun i =>
    if s i < ρ ω then
      (Δ : ℝ) * E (s i) * X.generator w (Y (s i)) else 0
  change (∑ i ∈ Finset.range m, A i) -
      (∑ i ∈ Finset.range m, C i) -
      (∑ i ∈ Finset.range m, G i) =
      (∑ i ∈ Finset.range m, (B i - C i - G i)) +
      (∑ i ∈ Finset.range m, (A i - B i))
  calc
    (∑ i ∈ Finset.range m, A i) -
        (∑ i ∈ Finset.range m, C i) -
        (∑ i ∈ Finset.range m, G i) =
        ∑ i ∈ Finset.range m, (A i - C i - G i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = ∑ i ∈ Finset.range m, ((B i - C i - G i) + (A i - B i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i ∈ Finset.range m, (B i - C i - G i)) +
        (∑ i ∈ Finset.range m, (A i - B i)) := by
      rw [Finset.sum_add_distrib]
