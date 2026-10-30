-- Prove2me | solution 10 for AvramDividend.Classical.barrier_value_scale_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T04:44:09.390835+00:00
-- url     : https://prove2.me/submissions/5fa969b2-5919-4c18-8303-cb08a496d283

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    0 < W a ∧
      dividendValue X q x (barrierStrategy X x a)
        = ENNReal.ofReal (W x / W a) * dividendValue X q a (barrierStrategy X a a) := by
  have hPos : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hExit : dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (W x / W a) * barrierSupValue X a q :=
    AvramDividend.Classical.barrierStrategy_value_eq_exit_factor X hX q hq W hW a ha x hx0 hxa
  have hSelf : dividendValue X q a (barrierStrategy X a a) = barrierSupValue X a q :=
    AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q a
  refine ⟨hPos, ?_⟩
  rw [hSelf]
  exact hExit
