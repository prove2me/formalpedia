-- Prove2me | solution 1 for AvramDividend.Classical.localized_terminal_integrable_from_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:43:36.636168+00:00
-- url     : https://prove2.me/submissions/0d61ba23-4732-48a4-89ec-520ffe94fcff

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_adapted
import Theorems.Thm_AvramDividend_Classical_survival_event_measurable_of_stopping_and_admissible
import Theorems.Thm_AvramDividend_Classical_capped_piecewise_test_measurable_of_continuousOn
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Any fixed finite reserve band gives integrable localised terminal values, even for infinite cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (T : ℝ≥0) :
    Integrable (fun ω =>
      if (T : ℝ≥0∞) < ruinTime X x D ω then
        if riskProcess X x D T ω ∈ Icc (0 : ℝ) B then
          w (riskProcess X x D T ω) else 0
      else 0) P := by
  haveI : IsProbabilityMeasure P := X.isProbability
  have hStop : IsStoppingTime 𝓕 (fun _ : Ω => (T : ℝ≥0∞)) :=
    isStoppingTime_const 𝓕 T
  have hSurvival : MeasurableSet
      {ω : Ω | (T : ℝ≥0∞) < ruinTime X x D ω} :=
    survival_event_measurable_of_stopping_and_admissible
      X x D hD (fun _ => (T : ℝ≥0∞)) hStop
  have hReserve : Measurable (riskProcess X x D T) :=
    (riskProcess_adapted X x D hD).measurable
  have hwCapped : ContinuousOn w (Icc (0 : ℝ) B) :=
    hw.mono (by intro y hy; exact hy.1)
  have hwPiece : Measurable
      (fun y : ℝ => if y ∈ Icc (0 : ℝ) B then w y else 0) :=
    capped_piecewise_test_measurable_of_continuousOn w B hwCapped
  have hPiece : Measurable
      (fun ω => if riskProcess X x D T ω ∈ Icc (0 : ℝ) B then
        w (riskProcess X x D T ω) else 0) :=
    hwPiece.comp hReserve
  have hMeas : Measurable (fun ω =>
      if (T : ℝ≥0∞) < ruinTime X x D ω then
        if riskProcess X x D T ω ∈ Icc (0 : ℝ) B then
          w (riskProcess X x D T ω) else 0
      else 0) :=
    Measurable.ite hSurvival hPiece measurable_const
  obtain ⟨M, hM0, hM⟩ :=
    continuous_test_abs_le_on_finite_cap w B hB hw
  apply Integrable.of_bound hMeas.aestronglyMeasurable M
  apply Filter.Eventually.of_forall
  intro ω
  change ‖if (T : ℝ≥0∞) < ruinTime X x D ω then
      (if riskProcess X x D T ω ∈ Icc (0 : ℝ) B then
        w (riskProcess X x D T ω) else 0) else 0‖ ≤ M
  by_cases hSurv : (T : ℝ≥0∞) < ruinTime X x D ω
  · by_cases hRange : riskProcess X x D T ω ∈ Icc (0 : ℝ) B
    · simpa only [if_pos hSurv, if_pos hRange, Real.norm_eq_abs] using
        hM _ hRange.1 hRange.2
    · simpa only [if_pos hSurv, if_neg hRange, norm_zero] using hM0
  · simpa only [if_neg hSurv, norm_zero] using hM0
