-- Prove2me | solution 6 for AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:38:54.156244+00:00
-- url     : https://prove2.me/submissions/9be786d7-22dd-4555-a565-562976548f20
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
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
  -- Repair of candidate 15033: the terminal CE was a duplicate `rw [hval]`
  -- after `rw [hself, hval]` had already eliminated every `barrierValue`
  -- redex (REWRITE_PATTERN_ABSENT). The second rewrite is deleted; the
  -- remaining goal is closed by the principal zero-barrier bridge.
  have hself : dividendValue X q 0 (barrierStrategy X 0 0) =
      barrierSupValue X 0 q :=
    AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q 0
  rw [hself]
  exact AvramDividend.Classical.zero_reflectedSupValue_eq_barrierValue
    X hX q hq W hW
