-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_finite_clock_large_mark_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:33:49.857056+00:00
-- url     : https://prove2.me/submissions/57e24a29-3636-4f04-9545-b5e22eb34ac9

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
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R : T → ℝ) (hR : Measurable R)
    (w : ℝ → ℝ) (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0)
    (hcap : ∀ t, R t ∈ Icc 0 v) :
    Integrable
      (fun p : T × ℝ =>
        if p.2 < -ε then w (R p.1 + p.2) - w (R p.1) else 0)
      (μ.prod (X.ν.restrict (Iio (-ε)))) := by
  have htail : X.ν (Iio (-ε)) < ⊤ :=
    avram_p4_c_generator_epsilon_large_jump_intensity_finite X ε hε
  haveI : IsFiniteMeasure (X.ν.restrict (Iio (-ε))) :=
    (isFiniteMeasure_restrict).2 (ne_of_lt htail)
  have hw_meas : Measurable w :=
    avram_p4_c_generator_zero_negative_payoff_measurable w hw_cont hw_neg
  obtain ⟨M, hM_nonneg, hM⟩ :=
    avram_p4_c_generator_large_raw_uniform_on_prejump_cap w v hv hw_cont hw_neg
  have hRprod : Measurable (fun p : T × ℝ => R p.1) :=
    hR.comp measurable_fst
  have hz : Measurable (fun p : T × ℝ => p.2) := measurable_snd
  have hraw : Measurable (fun p : T × ℝ =>
      w (R p.1 + p.2) - w (R p.1)) :=
    (hw_meas.comp (hRprod.add hz)).sub (hw_meas.comp hRprod)
  have hcut : MeasurableSet {p : T × ℝ | p.2 < -ε} :=
    measurableSet_Iio.preimage hz
  have hmeas : Measurable (fun p : T × ℝ =>
      if p.2 < -ε then w (R p.1 + p.2) - w (R p.1) else 0) :=
    Measurable.ite hcut hraw measurable_const
  apply Integrable.of_bound hmeas.aestronglyMeasurable M
  filter_upwards [] with p
  split_ifs with hp
  · have hpneg : p.2 < 0 := by linarith
    simpa only [Real.norm_eq_abs] using hM (R p.1) (hcap p.1) p.2 hpneg
  · simpa using hM_nonneg
