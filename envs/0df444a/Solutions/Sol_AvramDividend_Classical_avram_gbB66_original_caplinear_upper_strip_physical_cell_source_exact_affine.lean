-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB66_original_caplinear_upper_strip_physical_cell_source_exact_affine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:51:14.7782+00:00
-- url     : https://prove2.me/submissions/a09e0651-1323-4494-ab15-38733a24787b

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
    (x b : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m i : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let Y : ℝ := x + X.X s ω - rightLimit D s ω
    let Z : ℝ := x + X.X (s + Δ) ω - rightLimit D s ω
    let V : ℝ → ℝ := fun y =>
      if y ≤ b then w y else w b + (y - b)
    b < Y → b < Z →
      V Z - V Y = X.X (s + Δ) ω - X.X s ω := by
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let Y : ℝ := x + X.X s ω - rightLimit D s ω
  let Z : ℝ := x + X.X (s + Δ) ω - rightLimit D s ω
  let V : ℝ → ℝ := fun y =>
    if y ≤ b then w y else w b + (y - b)
  change b < Y → b < Z →
    V Z - V Y = X.X (s + Δ) ω - X.X s ω
  intro hy hz
  have hny : ¬ Y ≤ b := not_le.mpr hy
  have hnz : ¬ Z ≤ b := not_le.mpr hz
  simp only [V, if_neg hny, if_neg hnz]
  dsimp only [Y, Z]
  ring
