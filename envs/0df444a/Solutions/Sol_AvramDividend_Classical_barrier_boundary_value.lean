-- Prove2me | solution 1 for AvramDividend.Classical.barrier_boundary_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T17:44:34.985982+00:00
-- url     : https://prove2.me/submissions/199bb2de-7111-4392-9255-ce1fb36ef0d9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_scale_ratio

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    dividendValue X q a (barrierStrategy X a a) = ENNReal.ofReal (W a / deriv W a) := by
  calc
    dividendValue X q a (barrierStrategy X a a) =
        barrierSupValue X a q :=
      AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q a
    _ = ENNReal.ofReal (W a / deriv W a) :=
      AvramDividend.Classical.barrierSupValue_eq_scale_ratio X hX q hq W hW a ha
