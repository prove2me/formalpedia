-- Prove2me | solution 1 for AvramDividend.Classical.barrier_value_scale_factor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T17:47:07.486055+00:00
-- url     : https://prove2.me/submissions/c5b61ef2-e3f3-4246-9113-ea8e3816388f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    0 < W a ∧
      dividendValue X q x (barrierStrategy X x a) =
        ENNReal.ofReal (W x / W a) *
          dividendValue X q a (barrierStrategy X a a) := by
  constructor
  · exact scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  · have hfactor :=
      barrierStrategy_value_eq_exit_factor X hX q hq W hW a ha x hx0 hxa
    have hboundary :=
      barrierValue_self_eq_barrierSupValue X q a
    rw [hboundary]
    exact hfactor
