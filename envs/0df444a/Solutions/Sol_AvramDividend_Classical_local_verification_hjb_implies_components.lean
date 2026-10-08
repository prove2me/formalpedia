-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_hjb_implies_components
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:41:03.794269+00:00
-- url     : https://prove2.me/submissions/cea0d4b8-edfe-41ef-aaba-0cb2217004ca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (h : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0 ∧
      1 ≤ deriv w y := by
  intro y hy hyC
  obtain ⟨hInt, hMax⟩ := h y hy hyC
  have hDrift : X.generator w y - q * w y ≤ 0 :=
    (le_max_left (X.generator w y - q * w y)
      (1 - deriv w y)).trans_eq hMax
  have hGradient : 1 ≤ deriv w y := by
    have hGradPart : 1 - deriv w y ≤ 0 :=
      (le_max_right (X.generator w y - q * w y)
        (1 - deriv w y)).trans_eq hMax
    linarith
  exact ⟨hInt, hDrift, hGradient⟩
