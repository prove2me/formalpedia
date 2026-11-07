-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_original_ubv_zerojump_nonzero_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:35:52.923129+00:00
-- url     : https://prove2.me/submissions/30066bec-4484-46f6-acae-2c984fcd1991

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_purejump_ubv_infinite_variation

import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_ubv_purejump_nonzero_levy_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) : X.σ ≠ 0 := by
  intro hσ
  exact (avram_p4_f4_original_ubv_purejump_nonzero_levy_measure X hBV hσ) hν
