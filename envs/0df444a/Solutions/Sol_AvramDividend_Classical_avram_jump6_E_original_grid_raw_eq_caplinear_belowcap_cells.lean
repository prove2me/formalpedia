-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_E_original_grid_raw_eq_caplinear_belowcap_cells
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:04:09.436607+00:00
-- url     : https://prove2.me/submissions/0f48c8b9-f6d0-407e-9942-eef8b6375fa1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hV : ∀ y : ℝ, V y =
      if y ≤ C.toReal then w y else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (ω : Ω) (n j : ℕ)
    (hY : ∀ i < (n + 1) * (j + 1),
      x + X.X (min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω -
        rightLimit D (min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω ≤ C.toReal)
    (hZ : ∀ i < (n + 1) * (j + 1),
      x + X.X (min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω -
        rightLimit D (min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω ≤ C.toReal) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let m : ℕ := (n + 1) * (j + 1)
    (∑ i ∈ Finset.range m,
      E (v (i + 1)) * (w (Y (v (i + 1))) - w (Z i))) =
    (∑ i ∈ Finset.range m,
      E (v (i + 1)) * (V (Y (v (i + 1))) - V (Z i))) := by
  dsimp only
  apply Finset.sum_congr rfl
  intro i hi
  have hi : i < (n + 1) * (j + 1) := Finset.mem_range.mp hi
  have hy := hY i hi
  have hz := hZ i hi
  simp only [hV, if_pos hy, if_pos hz]
