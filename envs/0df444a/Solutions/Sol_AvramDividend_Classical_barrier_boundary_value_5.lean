-- Prove2me | solution 5 for AvramDividend.Classical.barrier_boundary_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:58:17.153825+00:00
-- url     : https://prove2.me/submissions/8cf1a7ac-97de-4292-a885-a779e6bc1d10
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_scale_ratio

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

-- 0443 via Proved 11b589b7 (self value = sup value) + Open a8d4c941 (sup value = scale ratio).
-- Binders verified live: 11b589b7 takes (X q a); a8d4 takes (X hX q hq W hW a ha).
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    dividendValue X q a (barrierStrategy X a a) = ENNReal.ofReal (W a / deriv W a) := by
  rw [AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q a]
  exact AvramDividend.Classical.barrierSupValue_eq_scale_ratio X hX q hq W hW a ha
