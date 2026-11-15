-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB69_original_physical_gaussian_caplinear_discounted_spatial_product_rule_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:16:58.327386+00:00
-- url     : https://prove2.me/submissions/59f1141b-51b3-40e9-a55b-b4f4c277ffd7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m i : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let Y : ℝ := x + X.X s ω - rightLimit D s ω
    let Z : ℝ := x + X.X (s + Δ) ω - rightLimit D s ω
    let V : ℝ → ℝ := fun y =>
      if y ≤ b then w y else w b + (y - b)
    Real.exp (-(q * ((s + Δ : ℝ≥0) : ℝ))) * V Z -
      Real.exp (-(q * (s : ℝ))) * V Y =
    Real.exp (-(q * (s : ℝ))) * (V Z - V Y) +
      (Real.exp (-(q * ((s + Δ : ℝ≥0) : ℝ))) -
        Real.exp (-(q * (s : ℝ)))) * V Z := by
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let Y : ℝ := x + X.X s ω - rightLimit D s ω
  let Z : ℝ := x + X.X (s + Δ) ω - rightLimit D s ω
  let V : ℝ → ℝ := fun y =>
    if y ≤ b then w y else w b + (y - b)
  change
    Real.exp (-(q * ((s + Δ : ℝ≥0) : ℝ))) * V Z -
      Real.exp (-(q * (s : ℝ))) * V Y =
    Real.exp (-(q * (s : ℝ))) * (V Z - V Y) +
      (Real.exp (-(q * ((s + Δ : ℝ≥0) : ℝ))) -
        Real.exp (-(q * (s : ℝ)))) * V Z
  ring
