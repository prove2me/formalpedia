-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_ordinary_deriv_zero_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:35:33.649992+00:00
-- url     : https://prove2.me/submissions/0942db1a-5aee-43f2-a43e-d4298f7e64e6

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : AvramDividend.Classical.IsScaleFunction X q W)
    (hzero : W 0 = 0) :
    deriv W 0 = 0 := by
  refine IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall fun y => ?_)
  rw [hzero]
  rcases lt_or_ge y 0 with h | h
  · exact (hW.1 y h).ge
  · exact hW.2.1 y h
