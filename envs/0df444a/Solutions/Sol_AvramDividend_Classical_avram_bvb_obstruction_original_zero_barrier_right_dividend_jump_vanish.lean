-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_zero_barrier_right_dividend_jump_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:51:18.556702+00:00
-- url     : https://prove2.me/submissions/4b38601f-4533-486b-b4b5-d8a5de3a2dff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_right_jump_of_initial_below_barrier
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) :
    rightLimit (barrierStrategy X 0 0) t ω -
      barrierStrategy X 0 0 t ω = 0 := by
  rw [barrierStrategy_no_right_jump_of_initial_below_barrier
    X 0 0 (le_refl 0) ω t]
  ring
