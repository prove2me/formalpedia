-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_w_nonneg_below_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:28:46.282373+00:00
-- url     : https://prove2.me/submissions/e5e35cde-b84c-44d0-bde7-364cc1102858

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_controls_dividend_jump_le_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (y : ℝ) (hy : 0 ≤ y) (hyC : ENNReal.ofReal y ≤ C) :
    0 ≤ w y := by
  have hJump :=
    local_verification_hjb_controls_dividend_jump_le_cap
      X q w C hw_cont hw_smooth hw_hjb
      y y hy le_rfl hyC
  have hDiff : y ≤ w y - w 0 := by
    simpa only [sub_self] using hJump
  linarith
