-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54cp_active_true_gaussian_physical_cell_lower_clipping_coefficients_redundant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T14:55:39.797097+00:00
-- url     : https://prove2.me/submissions/67ceedd2-66aa-455e-9c8c-b002095346ee

import Theorems.Thm_AvramDividend_Classical_avram_gbB54l_original_strict_physical_grid_postpayment_lower_clip_avoidance
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (j n m i : ℕ) (ω : Ω)
    (hMask : (i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) < ρ ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let y : ℝ := x + X.X s ω - rightLimit D s ω
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    (if y ∈ Icc a b then deriv w y else 1) =
      (if y ≤ b then deriv w y else 1) ∧
    (if y ∈ Icc a b then iteratedDeriv 2 w y else 0) =
      (if y ≤ b then iteratedDeriv 2 w y else 0) := by
  classical
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let y : ℝ := x + X.X s ω - rightLimit D s ω
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  have hLower : a ≤ y :=
    avram_gbB54l_original_strict_physical_grid_postpayment_lower_clip_avoidance
      X x D hD n m ρ δ hδ hFloor ω i hMask
  have hmem : y ∈ Icc a b ↔ y ≤ b := by
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨hLower, h⟩
  change (if y ∈ Icc a b then deriv w y else 1) =
      (if y ≤ b then deriv w y else 1) ∧
    (if y ∈ Icc a b then iteratedDeriv 2 w y else 0) =
      (if y ≤ b then iteratedDeriv 2 w y else 0)
  constructor <;> simp only [hmem]
