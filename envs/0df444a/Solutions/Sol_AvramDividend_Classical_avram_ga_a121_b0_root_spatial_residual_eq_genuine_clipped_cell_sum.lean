-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a121_b0_root_spatial_residual_eq_genuine_clipped_cell_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:04:34.309488+00:00
-- url     : https://prove2.me/submissions/617ddfc5-3b8b-4e3c-bb9b-5b394a249722

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section
/-- The original root stopped Gaussian three-sum spatial residual is exactly the sum of the genuinely clipped source-generator cell residuals. -/
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
    (∑ i ∈ Finset.range m, A i) -
      (∑ i ∈ Finset.range m, B i) -
      (∑ i ∈ Finset.range m, G i) =
    ∑ i ∈ Finset.range m, U i := by
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let v : ℕ → ℝ≥0 := fun i => min (s i) ρ
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
  let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
  let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
  let H : ℕ → ℝ := fun i => E (s i) * (deriv w (Y (s i)) * Z i +
    (iteratedDeriv 2 w (Y (s i)) / 2) * (Z i^2 - (Δ : ℝ) * X.σ^2)) +
    (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
  let A : ℕ → ℝ := fun i => E (v (i + 1)) *
    (w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) - w (Y (v i)))
  let B : ℕ → ℝ := fun i => if s i < ρ then E (s i) *
    (deriv w (Y (s i)) * Z i + (iteratedDeriv 2 w (Y (s i)) / 2) *
    (Z i^2 - (Δ : ℝ) * X.σ^2)) else 0
  let G : ℕ → ℝ := fun i => if s i < ρ then (Δ : ℝ) *
    E (s i) * X.generator w (Y (s i)) else 0
  let U : ℕ → ℝ := fun i => A i - (if s i < ρ then H i else 0)
  change (∑ i ∈ Finset.range m, A i) -
      (∑ i ∈ Finset.range m, B i) -
      (∑ i ∈ Finset.range m, G i) =
    ∑ i ∈ Finset.range m, U i
  have hCell (i : ℕ) : A i - B i - G i = U i := by
    dsimp only [U, A, B, G, H]
    by_cases hs : s i < ρ
    · simp only [if_pos hs]; ring
    · simp only [if_neg hs]; ring
  calc
    (∑ i ∈ Finset.range m, A i) -
      (∑ i ∈ Finset.range m, B i) -
      (∑ i ∈ Finset.range m, G i) =
        ∑ i ∈ Finset.range m, (A i - B i - G i) := by
          simp only [Finset.sum_sub_distrib]
    _ = ∑ i ∈ Finset.range m, U i :=
      Finset.sum_congr rfl (fun i hi => hCell i)
