-- Prove2me | solution 1 for AvramDividend.Classical.bv_generator_gradient_hjb_subsolution_inequality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:38:35.998366+00:00
-- url     : https://prove2.me/submissions/6a01e713-9e8e-45bf-a354-6e9d7ee769c3

import Mathlib.Data.Real.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Generator nonpositivity and derivative at least one imply the HJB subsolution inequality, even if neither component vanishes. This is the BV verification form. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      max (X.generator w y - q * w y) (1 - deriv w y) ≤ 0 := by
  intro y hy hcap
  apply max_le_iff.mpr
  exact ⟨(hgen y hy hcap).2, sub_nonpos.mpr (hgrad y hy hcap)⟩
