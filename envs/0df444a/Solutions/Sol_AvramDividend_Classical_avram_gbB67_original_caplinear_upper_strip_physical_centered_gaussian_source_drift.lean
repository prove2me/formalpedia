-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB67_original_caplinear_upper_strip_physical_centered_gaussian_source_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:01:07.944707+00:00
-- url     : https://prove2.me/submissions/e0b4ce8d-03a8-4b1a-b113-3d68b28b4cbd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB66_original_caplinear_upper_strip_physical_cell_source_exact_affine
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
    let centred : ℝ :=
      X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
    b < Y → b < Z →
      V Z - V Y - centred = (Δ : ℝ) * X.c := by
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let Y : ℝ := x + X.X s ω - rightLimit D s ω
  let Z : ℝ := x + X.X (s + Δ) ω - rightLimit D s ω
  let V : ℝ → ℝ := fun y =>
    if y ≤ b then w y else w b + (y - b)
  let centred : ℝ :=
    X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
  change b < Y → b < Z →
    V Z - V Y - centred = (Δ : ℝ) * X.c
  intro hy hz
  have hExact :=
    avram_gbB66_original_caplinear_upper_strip_physical_cell_source_exact_affine
      X x b w D ω n m i hy hz
  change V Z - V Y =
    X.X (s + Δ) ω - X.X s ω at hExact
  dsimp only [centred]
  linarith
