-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_strict_pos_of_unbounded_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T02:14:26.761207+00:00
-- url     : https://prove2.me/submissions/0984349e-60c3-44f1-8505-1192caa090d5

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_infinite_small_jump_moment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : ¬ X.BoundedVariation) :
    ∀ a : ℝ, 0 < a → 0 < W a := by
  rcases unbounded_variation_gaussian_or_infinite_small_jump_moment X hbv with
    hσ | hvar
  · intro a ha
    exact scaleFunction_strict_pos_of_gaussian X q W hW hσ a ha
  · exact scaleFunction_strict_pos_of_infinite_small_jump_moment
      X q W hW hvar
