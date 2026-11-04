-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_capped_original_large_jump_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:16:38.834025+00:00
-- url     : https://prove2.me/submissions/76f884bd-d42f-4117-b076-00599ae2770c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_zero_negative_payoff_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_large_raw_uniform_on_prejump_cap
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
    (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0) :
    ∀ y ∈ Icc 0 v,
      IntegrableOn (fun z : ℝ => w (y + z) - w y)
        (Iio (-ε)) X.ν := by
  have hw_meas : Measurable w :=
    avram_p4_c_generator_zero_negative_payoff_measurable w hw_cont hw_neg
  obtain ⟨M, _, hM⟩ :=
    avram_p4_c_generator_large_raw_uniform_on_prejump_cap w v hv hw_cont hw_neg
  intro y hy
  have htail : X.ν (Iio (-ε)) < ⊤ :=
    avram_p4_c_generator_epsilon_large_jump_intensity_finite X ε hε
  have hmeas : Measurable (fun z : ℝ => w (y + z) - w y) :=
    (hw_meas.comp (measurable_const.add measurable_id)).sub measurable_const
  apply IntegrableOn.of_bound htail hmeas.aestronglyMeasurable M
  filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
  change z < -ε at hz
  have hzneg : z < 0 := by linarith [hz, hε]
  simpa only [Real.norm_eq_abs] using hM y hy z hzneg
