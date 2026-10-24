-- Prove2me | solution 1 for AvramDividend.Classical.boundedVariation_min_one_abs_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:30:25.009787+00:00
-- url     : https://prove2.me/submissions/e9540320-a6c9-49cc-9a97-dfdcf4d50e6e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_scalar_majorant_integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The existing weighted BV moment lemma at coefficient one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    IntegrableOn (fun y : ℝ => min 1 |y|) (Iio 0) X.ν := by
  simpa only [one_mul] using
    (chat07_bv_negative_jump_scalar_majorant_integrable X hBV 1)
