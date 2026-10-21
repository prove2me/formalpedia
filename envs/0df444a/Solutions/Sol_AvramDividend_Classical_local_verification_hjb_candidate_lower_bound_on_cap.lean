-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_hjb_candidate_lower_bound_on_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:27:03.512992+00:00
-- url     : https://prove2.me/submissions/49d9d62e-13a7-4354-939a-e7f3ff3fe048

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
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
    (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (y : ℝ) (hy : 0 ≤ y) (hyC : ENNReal.ofReal y ≤ C) :
    y + w 0 ≤ w y ∧ 0 ≤ w y := by
  have hbound :
      y ≤ w y - w (y - y) :=
    local_verification_hjb_controls_dividend_jump_le_cap
      X q w C hw_cont hw_smooth hw_hjb y y hy le_rfl hyC
  simp only [sub_self] at hbound
  constructor <;> linarith
