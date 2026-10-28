-- Prove2me | solution 7 for AvramDividend.Classical.barrier_zero_boundary_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T11:48:54.997049+00:00
-- url     : https://prove2.me/submissions/e745a01a-a5aa-4536-8f0d-aba9324fbc3b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
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
  -- Principal argument: deterministic boundary bridge (Proved 11b589b7)
  -- rewrites the zero-barrier dividend value to the reflected-supremum value,
  -- then the zero-supremum scale identity (Open b83a725b, source-compatible)
  -- rewrites it to the analytic candidate. No sorry, no placeholder.
  have hdet : dividendValue X q 0 (barrierStrategy X 0 0) =
      barrierSupValue X 0 q :=
    AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q 0
  have hstoch : barrierSupValue X 0 q =
      ENNReal.ofReal (barrierValue W 0 0) :=
    AvramDividend.Classical.zero_reflectedSupValue_eq_barrierValue X hX q hq W hW
  calc dividendValue X q 0 (barrierStrategy X 0 0)
      = barrierSupValue X 0 q := hdet
    _ = ENNReal.ofReal (barrierValue W 0 0) := hstoch
