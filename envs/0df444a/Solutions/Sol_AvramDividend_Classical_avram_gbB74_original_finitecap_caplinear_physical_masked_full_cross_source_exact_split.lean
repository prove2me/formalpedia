-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB74_original_finitecap_caplinear_physical_masked_full_cross_source_exact_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:32:12.4102+00:00
-- url     : https://prove2.me/submissions/3e491459-1b5d-4df3-809b-4f8c48753aa2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a123_b0_original_root_exact_genuine_full_cross_residual_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (b q : ℝ)
    (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) :
    let Vb : ℝ → ℝ := fun y =>
      if y ≤ b then w y else w b + (y - b)
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun i => min (s i) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i =>
      E (s i) * (deriv Vb (Y (s i)) * Z i +
        (iteratedDeriv 2 Vb (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) +
        (Δ : ℝ) * E (s i) * X.generator Vb (Y (s i))
    let U : ℕ → ℝ := fun i =>
      E (v (i + 1)) *
        (Vb (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
          Vb (Y (v i))) -
      (if s i < ρ then H i else 0)
    let A : ℕ → ℝ := fun i =>
      E (v (i + 1)) * (Vb (x + X.X (v (i + 1)) ω -
        rightLimit D (v i) ω) - Vb (Y (v i)))
    let B : ℕ → ℝ := fun i =>
      if s i < ρ then E (s i) * (deriv Vb (Y (s i)) * Z i +
        (iteratedDeriv 2 Vb (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) else 0
    let G : ℕ → ℝ := fun i =>
      if s i < ρ then (Δ : ℝ) * E (s i) *
        X.generator Vb (Y (s i)) else 0
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (Vb (Y (s i) + R i) - Vb (Y (s i))) - H i
    let C : ℕ → ℝ := fun i =>
      E ρ * (Vb (Y (s i) + (X.X ρ ω - X.X (s i) ω)) -
        Vb (Y (s i))) - H i
    (∑ i ∈ Finset.range m, A i) -
      (∑ i ∈ Finset.range m, B i) -
      (∑ i ∈ Finset.range m, G i) =
      (∑ i ∈ Finset.range m,
        if s i < ρ ∧ s i + Δ ≤ ρ then F i else 0) +
      (∑ i ∈ Finset.range m,
        if s i < ρ ∧ ρ < s i + Δ then C i else 0) := by
  let Vb : ℝ → ℝ := fun y =>
    if y ≤ b then w y else w b + (y - b)
  exact avram_ga_a123_b0_original_root_exact_genuine_full_cross_residual_identity
    X x D Vb q ω n m ρ
