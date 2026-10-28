-- Prove2me | solution 10 for AvramDividend.Classical.barrier_zero_boundary_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:36:50.617483+00:00
-- url     : https://prove2.me/submissions/9cb0acbb-b5e8-4148-9d98-0b57e7023cf3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_eq_barrierValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by
  have h1 : dividendValue X q 0 (barrierStrategy X 0 0) = barrierSupValue X 0 q :=
    AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q 0
  have h2 : barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) :=
    AvramDividend.Classical.zero_reflectedSupValue_eq_barrierValue X hX q hq W hW
  exact h1.trans h2
