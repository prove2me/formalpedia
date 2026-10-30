-- Prove2me | solution 5 for AvramDividend.Classical.barrier_value_scale_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:32:53.622977+00:00
-- url     : https://prove2.me/submissions/62f10a0c-d4cf-42aa-8a52-1f44a2b10779

import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The scale ratio for a barrier strategy follows from the first-exit factor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    0 < W a ∧
      dividendValue X q x (barrierStrategy X x a) =
        ENNReal.ofReal (W x / W a) *
          dividendValue X q a (barrierStrategy X a a) := by
  constructor
  · exact scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  · calc
      dividendValue X q x (barrierStrategy X x a) =
          ENNReal.ofReal (W x / W a) * barrierSupValue X a q :=
        barrierStrategy_value_eq_exit_factor X hX q hq W hW a ha x hx0 hxa
      _ = ENNReal.ofReal (W x / W a) *
          dividendValue X q a (barrierStrategy X a a) := by
        rw [barrierValue_self_eq_barrierSupValue X q a]
