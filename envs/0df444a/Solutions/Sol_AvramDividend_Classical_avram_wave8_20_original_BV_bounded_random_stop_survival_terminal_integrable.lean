-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_BV_bounded_random_stop_survival_terminal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:14:03.446512+00:00
-- url     : https://prove2.me/submissions/07a42de3-8266-49a8-b4ae-8fa15e34d8b2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_random_clock_survival_terminal_ae_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopped_postPayment_reserve_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Genuine stopped terminal L1 follows from one random-clock envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτStop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτBound : ∀ ω, τ ω ≤ H) :
    Integrable (fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) P := by
  classical
  haveI : IsProbabilityMeasure P := X.isProbability
  have hStrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hτNN : Measurable τ :=
    measurable_coe_nnreal_ennreal_iff.mp hτStop.measurable'
  have hτReal : Measurable (fun ω => (τ ω : ℝ)) :=
    measurable_coe_nnreal_real.comp hτNN
  have hτENN : Measurable (fun ω => (τ ω : ℝ≥0∞)) :=
    hτStop.measurable'
  have hYMeas : Measurable (fun ω =>
      x + X.X (τ ω) ω - rightLimit D (τ ω) ω) :=
    avram_wave6_06_original_rightcont_stopped_postPayment_reserve_measurable
      X x D hStrat τ hτStop
  have hSurvMeas : MeasurableSet
      {ω | (τ ω : ℝ≥0∞) < ruinTime X x D ω} :=
    measurableSet_lt hτENN (ruinTime_measurable X x D hStrat)
  have hWMeas : Measurable w :=
    (local_verification_candidate_borel_and_postPayment_adapted
      X x D hStrat w hw_cont hw_neg).1
  have hExpMeas : Measurable
      (fun ω => Real.exp (-(q * (τ ω : ℝ)))) :=
    Real.continuous_exp.measurable.comp
      ((measurable_const.mul hτReal).neg)
  have hMaxMeas : Measurable (fun ω =>
      max 0 (Real.exp (-(q * (τ ω : ℝ))) *
        w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))) :=
    measurable_const.max (hExpMeas.mul (hWMeas.comp hYMeas))
  have hTermMeas : Measurable (fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) :=
    Measurable.ite hSurvMeas hMaxMeas measurable_const
  obtain ⟨K, hK0, hK⟩ :=
    avram_wave8_20_original_BV_bounded_random_clock_survival_terminal_ae_bound
      X hX hBV q hq w hw_cont x C D hD H τ hτBound
  apply Integrable.of_bound hTermMeas.aestronglyMeasurable K
  filter_upwards [hK] with ω hKω
  have hNonneg : 0 ≤
      (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) := by
    by_cases hs : (τ ω : ℝ≥0∞) < ruinTime X x D ω
    · simpa only [if_pos hs] using
        (le_max_left (0 : ℝ)
          (Real.exp (-(q * (τ ω : ℝ))) *
            w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)))
    · simp only [if_neg hs, le_refl]
  simpa only [Real.norm_eq_abs, abs_of_nonneg hNonneg] using hKω
