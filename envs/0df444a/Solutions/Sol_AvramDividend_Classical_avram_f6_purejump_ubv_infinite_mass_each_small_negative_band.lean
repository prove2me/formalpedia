-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_purejump_ubv_infinite_mass_each_small_negative_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:32:20.501203+00:00
-- url     : https://prove2.me/submissions/a07db3da-d0e9-41ac-aa81-4e47567b7daf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_purejump_ubv_negative_jump_intensity_infinite
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
import Theorems.Thm_AvramDividend_Classical_avram_f6_infinite_negative_mass_localised_near_zero
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
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    X.ν (Ioo (-δ) 0) = ⊤ := by
  have hTotal : X.ν (Iio (0 : ℝ)) = ⊤ :=
    avram_f6_purejump_ubv_negative_jump_intensity_infinite X hBV hσ
  have hTail : X.ν (Iic (-δ)) < ⊤ :=
    negative_jump_truncation_measure_finite X.ν X.ν_integrable δ hδ
  exact avram_f6_infinite_negative_mass_localised_near_zero
    X.ν δ hδ hTotal hTail
