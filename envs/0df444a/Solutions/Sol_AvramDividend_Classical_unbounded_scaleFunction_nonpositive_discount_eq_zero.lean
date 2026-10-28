-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scaleFunction_nonpositive_discount_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:30:53.697184+00:00
-- url     : https://prove2.me/submissions/7dea1901-1a03-4b5f-9788-8590c034d4db

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_scaleFunction_negative_q_impossible
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Any scale function of an unbounded-variation process with nonpositive discount has q=0. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : q ≤ 0)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) : q = 0 := by
  rcases lt_or_eq_of_le hq with hneg | heq
  · exact False.elim
      (unbounded_scaleFunction_negative_q_impossible X q hneg W hW hnbv)
  · exact heq
