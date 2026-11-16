-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54cp_true_physical_gaussian_source_lower_clip_coefficients_sum_rewrite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:11:14.996801+00:00
-- url     : https://prove2.me/submissions/bcc9b1d3-47ea-4275-a480-6d47f3c8159a

import Theorems.Thm_AvramDividend_Classical_avram_gbB54cp_active_true_gaussian_physical_cell_lower_clipping_coefficients_redundant
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (j n : ℕ) :
      let M : ℕ → Ω → ℝ := fun m ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η =>
          x + X.X (s i) η - rightLimit D (s i) η
        let Z : ℕ → Ω → ℝ := fun i η =>
          X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
        let G : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then deriv w (Y i η) else 1)
          else 0
        let H : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then (1 / 2 : ℝ) *
            Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0)
          else 0
        (Finset.range (m + 1)).sum (fun i =>
          G i ω * Z i ω + H i ω *
            (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      let Upper : ℕ → Ω → ℝ := fun m ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η =>
          x + X.X (s i) η - rightLimit D (s i) η
        let Z : ℕ → Ω → ℝ := fun i η =>
          X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
        let G : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ≤ b then deriv w (Y i η) else 1)
          else 0
        let H : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then (1 / 2 : ℝ) *
            Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ≤ b then iteratedDeriv 2 w (Y i η) else 0)
          else 0
        (Finset.range (m + 1)).sum (fun i =>
          G i ω * Z i ω + H i ω *
            (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2)) 
      ∀ (m : ℕ) (ω : Ω), M m ω = Upper m ω := by
  classical
  intro M Upper m ω
  dsimp only [M, Upper]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hMask : (i : ℝ≥0) *
      ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) < ρ ω
  · have hPair :=
      avram_gbB54cp_active_true_gaussian_physical_cell_lower_clipping_coefficients_redundant
        X x D hD ρ δ hδ hFloor w C j n m i ω hMask
    simp only [if_pos hMask, hPair.1, hPair.2]
  · simp only [if_neg hMask]
