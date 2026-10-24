-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_strict_pos_of_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:12:31.442576+00:00
-- url     : https://prove2.me/submissions/59674c6f-ac65-48dd-9e71-3cdf558508f1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! The accepted unbounded-variation positivity theorem has the exact target type. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : ¬ X.BoundedVariation) :
    ∀ a : ℝ, 0 < a → 0 < W a := by
  exact AvramDividend.Classical.scaleFunction_strict_pos_of_unbounded_variation
    X q W hW hbv
