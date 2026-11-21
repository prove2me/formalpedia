-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_E_original_cell_prepaid_le_cap_of_margin_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:04:16.820741+00:00
-- url     : https://prove2.me/submissions/325a1bf6-5e9c-47a9-8800-17fb45f27364

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
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (ω : Ω) (n j : ℕ) (δ : ℝ)
    (hMargin : ∀ i < (n + 1) * (j + 1),
      x + X.X (min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω -
        rightLimit D (min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω
        ≤ C.toReal - δ)
    (hVariation : ∀ i < (n + 1) * (j + 1),
      rightLimit D (min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω -
        rightLimit D (min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω ≤ δ) :
    ∀ i < (n + 1) * (j + 1),
      x + X.X (min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω -
        rightLimit D (min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω ≤ C.toReal := by
  intro i hi
  have hm := hMargin i hi
  have hv := hVariation i hi
  linarith
