-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_purejump_ubv_truncated_negative_rates_diverge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:04:56.919203+00:00
-- url     : https://prove2.me/submissions/0b0e866a-2824-43ab-9edc-1342b6aa2a85

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_purejump_ubv_negative_jump_intensity_infinite
import Theorems.Thm_AvramDividend_Classical_negative_jump_real_tail_tendsto_top
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) :
    Tendsto (fun δ : ℝ => (X.ν (Iio (-δ))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  have hMass : X.ν (Iio (0 : ℝ)) = ⊤ :=
    avram_f6_purejump_ubv_negative_jump_intensity_infinite X hBV hσ
  exact negative_jump_real_tail_tendsto_top X.ν X.ν_integrable hMass
