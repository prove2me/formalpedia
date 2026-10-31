-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_standing_barrierSupValue_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:37:37.310737+00:00
-- url     : https://prove2.me/submissions/e0b8789d-9af5-46d5-9e29-1563c9247b8d

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_finite_step_upper
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine killed reflected-regulator value is finite at every positive
barrier under Standing, without any derivative or C1 hypothesis on W. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    barrierSupValue X a q < ⊤ := by
  exact lt_of_le_of_lt
    (avram_wave3_02_standing_finite_step_upper X hX q hq W hW a ha)
    ENNReal.ofReal_lt_top
