-- Prove2me | solution 6 for AvramDividend.Classical.barrier_value_scale_factor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T06:17:52.975108+00:00
-- url     : https://prove2.me/submissions/c5650eec-4b48-4b3e-abb9-2ea94b141c0a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The value at any reserve below a positive barrier factors through the value at that barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
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
  · rw [barrierStrategy_value_eq_exit_factor X hX q hq W hW a ha x hx0 hxa,
      barrierValue_self_eq_barrierSupValue X q a]
