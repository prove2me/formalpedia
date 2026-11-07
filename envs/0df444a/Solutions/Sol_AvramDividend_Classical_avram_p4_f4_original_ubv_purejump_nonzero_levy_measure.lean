-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_original_ubv_purejump_nonzero_levy_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:49:37.38755+00:00
-- url     : https://prove2.me/submissions/37c0e9c0-0026-4476-834f-b7b25e46a93f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_purejump_ubv_infinite_variation

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
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) : X.ν ≠ 0 := by
  intro hν
  have hInf := avram_p4_f4_original_purejump_ubv_infinite_variation X hBV hσ
  simp [hν] at hInf
