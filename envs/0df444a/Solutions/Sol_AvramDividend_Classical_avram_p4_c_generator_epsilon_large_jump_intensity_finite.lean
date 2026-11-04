-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_epsilon_large_jump_intensity_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:26:44.025032+00:00
-- url     : https://prove2.me/submissions/6fe48d0b-ea2a-4931-96f2-4329503effbd

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ε : ℝ) (hε : 0 < ε) :
    X.ν (Iio (-ε)) < ⊤ := by
  have htail : X.ν (Iic (-ε)) < ⊤ :=
    negative_jump_truncation_measure_finite X.ν X.ν_integrable ε hε
  have hsub : Iio (-ε) ⊆ Iic (-ε) := by
    intro z hz
    change z < -ε at hz
    change z ≤ -ε
    exact le_of_lt hz
  exact lt_of_le_of_lt (measure_mono hsub) htail
