-- Prove2me | solution 1 for AvramDividend.Classical.localized_stopping_terminal_integrable_from_progressive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:46:12.644822+00:00
-- url     : https://prove2.me/submissions/dae38fd0-e438-4818-a005-3bf0570b3be6

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_survival_event_measurable_of_stopping_and_admissible
import Theorems.Thm_AvramDividend_Classical_capped_piecewise_test_measurable_of_continuousOn
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Localisation in any finite reserve band gives integrability at an arbitrary stopping time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (hProg : ProgMeasurable 𝓕 (riskProcess X x D)) :
    Integrable (fun ω =>
      if τ ω < ruinTime X x D ω then
        if stoppedValue (riskProcess X x D) τ ω ∈ Icc (0 : ℝ) B then
          w (stoppedValue (riskProcess X x D) τ ω) else 0
      else 0) P := by
  haveI : IsProbabilityMeasure P := X.isProbability
  have hSurvival : MeasurableSet {ω : Ω | τ ω < ruinTime X x D ω} :=
    survival_event_measurable_of_stopping_and_admissible
      X x D hD τ hτ
  have hReserve : Measurable (stoppedValue (riskProcess X x D) τ) :=
    (measurable_stoppedValue hProg hτ).mono hτ.measurableSpace_le le_rfl
  have hwCapped : ContinuousOn w (Icc (0 : ℝ) B) :=
    hw.mono (by intro y hy; exact hy.1)
  have hwPiece : Measurable
      (fun y : ℝ => if y ∈ Icc (0 : ℝ) B then w y else 0) :=
    capped_piecewise_test_measurable_of_continuousOn w B hwCapped
  have hPiece : Measurable
      (fun ω => if stoppedValue (riskProcess X x D) τ ω ∈ Icc (0 : ℝ) B then
        w (stoppedValue (riskProcess X x D) τ ω) else 0) :=
    hwPiece.comp hReserve
  have hTerminal : Measurable (fun ω =>
      if τ ω < ruinTime X x D ω then
        if stoppedValue (riskProcess X x D) τ ω ∈ Icc (0 : ℝ) B then
          w (stoppedValue (riskProcess X x D) τ ω) else 0
      else 0) :=
    Measurable.ite hSurvival hPiece measurable_const
  obtain ⟨M, hM0, hM⟩ :=
    continuous_test_abs_le_on_finite_cap w B hB hw
  apply Integrable.of_bound hTerminal.aestronglyMeasurable M
  apply Filter.Eventually.of_forall
  intro ω
  change ‖if τ ω < ruinTime X x D ω then
      (if stoppedValue (riskProcess X x D) τ ω ∈ Icc (0 : ℝ) B then
        w (stoppedValue (riskProcess X x D) τ ω) else 0) else 0‖ ≤ M
  by_cases hSurv : τ ω < ruinTime X x D ω
  · by_cases hRange : stoppedValue (riskProcess X x D) τ ω ∈ Icc (0 : ℝ) B
    · simpa only [if_pos hSurv, if_pos hRange, Real.norm_eq_abs] using
        hM _ hRange.1 hRange.2
    · simpa only [if_pos hSurv, if_neg hRange, norm_zero] using hM0
  · simpa only [if_neg hSurv, norm_zero] using hM0
