-- Prove2me | solution 17 for AvramDividend.Classical.barrier_strategy_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T21:53:58.787527+00:00
-- url     : https://prove2.me/submissions/cc8645d2-c54c-4d00-87e8-212e0bee1ce4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_value_scale_factor
import Theorems.Thm_AvramDividend_Classical_barrier_boundary_value
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
import Theorems.Thm_AvramDividend_Classical_ennreal_scale_ratio_cancel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) = ENNReal.ofReal (W x / deriv W a) := by
  obtain ⟨hWa, hScale⟩ :=
    AvramDividend.Classical.barrier_value_scale_factor X hX q hq W hW a ha x hx0 hxa
  have hBoundary :
      dividendValue X q a (barrierStrategy X a a) = ENNReal.ofReal (W a / deriv W a) :=
    AvramDividend.Classical.barrier_boundary_value X hX q hq W hW a ha
  have hderiv : 0 < deriv W a :=
    AvramDividend.Classical.scaleDeriv_pos X hX q hq W hW a ha
  calc
    dividendValue X q x (barrierStrategy X x a)
        = ENNReal.ofReal (W x / W a) * dividendValue X q a (barrierStrategy X a a) := hScale
    _ = ENNReal.ofReal (W x / W a) * ENNReal.ofReal (W a / deriv W a) := by rw [hBoundary]
    _ = ENNReal.ofReal (W x / deriv W a) :=
      AvramDividend.Classical.ennreal_scale_ratio_cancel
        (W x) (W a) (deriv W a) (hW.2.1 x hx0) hWa hderiv
