-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB79_original_finitecap_true_B54_gaussian_upperstrip_coefficients_affine_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:40:49.577747+00:00
-- url     : https://prove2.me/submissions/e45b3009-e5ac-4304-9871-fb1a7a2c78f4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q δ : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0)
    (n m j i : ℕ) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let Y : ℝ := x + X.X s ω - rightLimit D s ω
    let G : ℝ :=
      if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
        (if Y ∈ Icc a b then deriv w Y else 1)
      else 0
    let H : ℝ :=
      if s < ρ ω then (1 / 2 : ℝ) *
        Real.exp (-(q * (s : ℝ))) *
        (if Y ∈ Icc a b then iteratedDeriv 2 w Y else 0)
      else 0
    s < ρ ω → b < Y →
      G = Real.exp (-(q * (s : ℝ))) ∧ H = 0 := by
  classical
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal *
    (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Y : ℝ := x + X.X s ω - rightLimit D s ω
  let G : ℝ :=
    if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
      (if Y ∈ Icc a b then deriv w Y else 1)
    else 0
  let H : ℝ :=
    if s < ρ ω then (1 / 2 : ℝ) *
      Real.exp (-(q * (s : ℝ))) *
      (if Y ∈ Icc a b then iteratedDeriv 2 w Y else 0)
    else 0
  change s < ρ ω → b < Y →
    G = Real.exp (-(q * (s : ℝ))) ∧ H = 0
  intro hs hY
  have hnot : Y ∉ Icc a b := by
    intro hh
    exact (not_le_of_gt hY) hh.2
  simp [G, H, hs, hnot]
