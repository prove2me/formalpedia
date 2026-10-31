-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_pointwise_ratio_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:22:26.945556+00:00
-- url     : https://prove2.me/submissions/2169bab6-fab8-4b94-9d8f-7e2101c7ce31

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The original reflected dividend scale quotient is nondecreasing at
arbitrary two positive points of differentiability, without global C1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (hda : DifferentiableAt ℝ W a)
    (hdb : DifferentiableAt ℝ W b) :
    ENNReal.ofReal (W a / deriv W a) ≤
      ENNReal.ofReal (W b / deriv W b) := by
  calc
    ENNReal.ofReal (W a / deriv W a) = barrierSupValue X a q :=
      (avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
        X hX q hq W hW a ha hda).symm
    _ ≤ barrierSupValue X b q := barrierSupValue_mono_barrier X a b q hab
    _ = ENNReal.ofReal (W b / deriv W b) :=
      avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
        X hX q hq W hW b hb hdb
