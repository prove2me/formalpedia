-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_large_raw_integrable_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:13:42.062559+00:00
-- url     : https://prove2.me/submissions/76281b36-303b-4d9f-b7e3-e29cc7cf57f1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (y ε M : ℝ) (hε : 0 < ε) (hw_meas : Measurable w)
    (hbound : ∀ z : ℝ, z < -ε →
      |w (y + z) - w y| ≤ M) :
    IntegrableOn (fun z : ℝ => w (y + z) - w y)
      (Iio (-ε)) X.ν := by
  have htail : X.ν (Iio (-ε)) < ⊤ :=
    avram_p4_c_generator_epsilon_large_jump_intensity_finite X ε hε
  have hmeas : Measurable (fun z : ℝ => w (y + z) - w y) :=
    (hw_meas.comp (measurable_const.add measurable_id)).sub measurable_const
  apply IntegrableOn.of_bound htail hmeas.aestronglyMeasurable M
  filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
  change z < -ε at hz
  simpa only [Real.norm_eq_abs] using hbound z hz
