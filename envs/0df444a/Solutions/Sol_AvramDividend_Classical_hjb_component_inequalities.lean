-- Prove2me | solution 1 for AvramDividend.Classical.hjb_component_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T19:44:13.309986+00:00
-- url     : https://prove2.me/submissions/f8d50c3d-838f-4b4b-823b-3a0186b7ffff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option autoImplicit false
set_option linter.all false

open AvramDividend AvramDividend.Classical in open MeasureTheory Set in open scoped NNReal ENNReal in open AvramDividend.Classical in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (y : ℝ) (hy : 0 < y) (hyC : ENNReal.ofReal y < C) :
    X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0 ∧
      1 ≤ deriv w y := by
  intros
  grind
