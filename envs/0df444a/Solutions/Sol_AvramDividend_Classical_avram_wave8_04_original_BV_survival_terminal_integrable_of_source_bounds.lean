-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_04_original_BV_survival_terminal_integrable_of_source_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:42:14.182086+00:00
-- url     : https://prove2.me/submissions/a94b96e9-fcf9-49e2-84ba-7d1a11c50b0e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_04_original_BV_postright_terminal_drift_ceiling_ae
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hInitial : ∀ ω, 0 ≤ rightLimit D 0 ω)
    (S : ℝ≥0)
    (hPostMeas : Measurable (fun ω =>
      x + X.X S ω - rightLimit D S ω))
    (hSurvivalMeas : MeasurableSet
      {ω | (S : ℝ≥0∞) < ruinTime X x D ω})
    (hSurvivalNonneg : ∀ᵐ ω ∂P,
      (S : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ x + X.X S ω - rightLimit D S ω) :
    Integrable (fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (S : ℝ))) *
          w (x + X.X S ω - rightLimit D S ω))
      else 0) P := by
  classical
  haveI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → ℝ := fun ω => x + X.X S ω - rightLimit D S ω
  let B : ℝ := max 0 (x + (S : ℝ) * X.drift)
  have hB : 0 ≤ B := le_max_left _ _
  obtain ⟨M, hM0, hM⟩ :=
    continuous_test_abs_le_on_finite_cap w B hB hw_cont
  have hWMeas : Measurable w :=
    (local_verification_candidate_borel_and_postPayment_adapted
      X x D hD w hw_cont hw_neg).1
  have hYMeas : Measurable Y := hPostMeas
  have hValueMeas : Measurable
      (fun ω => Real.exp (-(q * (S : ℝ))) * w (Y ω)) :=
    measurable_const.mul (hWMeas.comp hYMeas)
  have hMaxMeas : Measurable
      (fun ω => max 0 (Real.exp (-(q * (S : ℝ))) * w (Y ω))) :=
    measurable_const.max hValueMeas
  have hTermMeas : Measurable
      (fun ω => if (S : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (S : ℝ))) * w (Y ω)) else 0) :=
    Measurable.ite hSurvivalMeas hMaxMeas measurable_const
  have hCeiling : ∀ᵐ ω ∂P,
      Y ω ≤ x + (S : ℝ) * X.drift :=
    avram_wave7_04_original_BV_postright_terminal_drift_ceiling_ae
      X hBV x D hD hInitial S
  let Bound : ℝ := Real.exp (-(q * (S : ℝ))) * M
  have hBoundNonneg : 0 ≤ Bound :=
    mul_nonneg (Real.exp_nonneg _) hM0
  apply Integrable.of_bound hTermMeas.aestronglyMeasurable Bound
  filter_upwards [hCeiling, hSurvivalNonneg] with ω hCeil hLower
  change ‖if (S : ℝ≥0∞) < ruinTime X x D ω then
    max 0 (Real.exp (-(q * (S : ℝ))) * w (Y ω)) else 0‖ ≤ Bound
  by_cases hSurv : (S : ℝ≥0∞) < ruinTime X x D ω
  · have hY0 : 0 ≤ Y ω := hLower hSurv
    have hYB : Y ω ≤ B :=
      le_trans hCeil (le_max_right _ _)
    have hAbs : |w (Y ω)| ≤ M := hM (Y ω) hY0 hYB
    have hWU : w (Y ω) ≤ M := (abs_le.mp hAbs).2
    have hExp : 0 ≤ Real.exp (-(q * (S : ℝ))) := Real.exp_nonneg _
    have hProduct : Real.exp (-(q * (S : ℝ))) * w (Y ω) ≤ Bound :=
      mul_le_mul_of_nonneg_left hWU hExp
    have hMaxLower :
        0 ≤ max 0 (Real.exp (-(q * (S : ℝ))) * w (Y ω)) :=
      le_max_left _ _
    have hMaxUpper :
        max 0 (Real.exp (-(q * (S : ℝ))) * w (Y ω)) ≤ Bound :=
      max_le hBoundNonneg hProduct
    simpa only [if_pos hSurv, Real.norm_eq_abs,
      abs_of_nonneg hMaxLower] using hMaxUpper
  · simpa only [if_neg hSurv, norm_zero] using hBoundNonneg
