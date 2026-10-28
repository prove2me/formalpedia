-- Prove2me | solution 1 for AvramDividend.Classical.capped_survival_stopped_test_aestronglyMeasurable_of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:38:11.682958+00:00
-- url     : https://prove2.me/submissions/df6c3c90-b339-409c-bf4c-b88f8879d9ad

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_survival_event_measurable_of_stopping_and_admissible
import Theorems.Thm_AvramDividend_Classical_capped_piecewise_test_measurable_of_continuousOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Compact-cap continuity suffices for measurable stopped HJB terminal values. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (B : ℝ)
    (hw : ContinuousOn w (Icc (0 : ℝ) B))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (hProg : ProgMeasurable 𝓕 (riskProcess X x D))
    (hCap : ∀ ω, τ ω < ruinTime X x D ω →
      stoppedValue (riskProcess X x D) τ ω ∈ Icc (0 : ℝ) B) :
    AEStronglyMeasurable
      (fun ω => if τ ω < ruinTime X x D ω then
        w (stoppedValue (riskProcess X x D) τ ω) else 0) P := by
  have hSurvival : MeasurableSet {ω : Ω | τ ω < ruinTime X x D ω} :=
    survival_event_measurable_of_stopping_and_admissible X x D hD τ hτ
  have hReserve : Measurable (stoppedValue (riskProcess X x D) τ) :=
    (measurable_stoppedValue hProg hτ).mono hτ.measurableSpace_le le_rfl
  have hwPiece : Measurable
      (fun y : ℝ => if y ∈ Icc (0 : ℝ) B then w y else 0) :=
    capped_piecewise_test_measurable_of_continuousOn w B hw
  have hPiece : Measurable
      (fun ω => if stoppedValue (riskProcess X x D) τ ω ∈ Icc (0 : ℝ) B then
        w (stoppedValue (riskProcess X x D) τ ω) else 0) :=
    hwPiece.comp hReserve
  have hTerminal : Measurable
      (fun ω => if τ ω < ruinTime X x D ω then
        (if stoppedValue (riskProcess X x D) τ ω ∈ Icc (0 : ℝ) B then
          w (stoppedValue (riskProcess X x D) τ ω) else 0) else 0) :=
    Measurable.ite hSurvival hPiece measurable_const
  have hEq :
      (fun ω => if τ ω < ruinTime X x D ω then
        w (stoppedValue (riskProcess X x D) τ ω) else 0) =
      (fun ω => if τ ω < ruinTime X x D ω then
        (if stoppedValue (riskProcess X x D) τ ω ∈ Icc (0 : ℝ) B then
          w (stoppedValue (riskProcess X x D) τ ω) else 0) else 0) := by
    funext ω
    by_cases h : τ ω < ruinTime X x D ω
    · simp only [if_pos h, if_pos (hCap ω h)]
    · simp only [if_neg h]
  rw [hEq]
  exact hTerminal.aestronglyMeasurable
