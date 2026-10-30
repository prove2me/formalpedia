-- Prove2me | solution 9 for AvramDividend.Classical.barrier_value_scale_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:33:07.883865+00:00
-- url     : https://prove2.me/submissions/1d88ba28-7775-4b10-ba73-447840ce1088

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Positive-barrier value factorisation via the published exit-factor identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    0 < W a ∧
      dividendValue X q x (barrierStrategy X x a) =
        ENNReal.ofReal (W x / W a) *
          dividendValue X q a (barrierStrategy X a a) := by
  constructor
  · exact scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  · rw [barrierStrategy_value_eq_exit_factor
      X hX q hq W hW a ha x hx0 hxa]
    exact congrArg (fun v : ℝ≥0∞ => ENNReal.ofReal (W x / W a) * v)
      (barrierValue_self_eq_barrierSupValue X q a).symm
