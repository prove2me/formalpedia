-- Prove2me | solution 1 for AvramDividend.Classical.chat07_bv_negative_jump_scalar_majorant_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:49:57.083977+00:00
-- url     : https://prove2.me/submissions/4c9a7159-3689-4d79-af90-2613c50ce256

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_min_abs_integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The bounded-variation negative-jump first moment absorbs any fixed scalar envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (C : ℝ) :
    IntegrableOn (fun y : ℝ => C * min 1 |y|) (Iio (0 : ℝ)) X.ν := by
  exact (chat07_bv_negative_jump_min_abs_integrable X hBV).const_mul C
