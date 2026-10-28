-- Prove2me | solution 1 for AvramDividend.Classical.capped_deterministic_terminal_integrable_from_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:16:57.955676+00:00
-- url     : https://prove2.me/submissions/ea8a0fa2-f02c-4ef8-8cba-85e8efffbe29

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_adapted
import Theorems.Thm_AvramDividend_Classical_survival_event_measurable_of_stopping_and_admissible
import Theorems.Thm_AvramDividend_Classical_capped_piecewise_test_measurable_of_continuousOn
import Theorems.Thm_AvramDividend_Classical_capped_surviving_riskProcess_range_real_finite
import Theorems.Thm_AvramDividend_Classical_capped_surviving_terminal_test_integrable_of_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Fixed-time survival payoffs are integrable using adaptedness alone. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (T : ℝ≥0) :
    Integrable (fun ω =>
      if (T : ℝ≥0∞) < ruinTime X x D ω then
        w (riskProcess X x D T ω) else 0) P := by
  have hStrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hStop : IsStoppingTime 𝓕 (fun _ : Ω => (T : ℝ≥0∞)) :=
    isStoppingTime_const 𝓕 T
  have hSurvival : MeasurableSet
      {ω : Ω | (T : ℝ≥0∞) < ruinTime X x D ω} :=
    survival_event_measurable_of_stopping_and_admissible
      X x D hStrat (fun _ => (T : ℝ≥0∞)) hStop
  have hReserve : Measurable (riskProcess X x D T) :=
    (riskProcess_adapted X x D hStrat).measurable
  have hwCapped : ContinuousOn w (Icc (0 : ℝ) B) :=
    hw.mono (by intro y hy; exact hy.1)
  have hwPiece : Measurable
      (fun y : ℝ => if y ∈ Icc (0 : ℝ) B then w y else 0) :=
    capped_piecewise_test_measurable_of_continuousOn w B hwCapped
  have hPiece : Measurable
      (fun ω => if riskProcess X x D T ω ∈ Icc (0 : ℝ) B then
        w (riskProcess X x D T ω) else 0) :=
    hwPiece.comp hReserve
  have hTerminal : Measurable
      (fun ω => if (T : ℝ≥0∞) < ruinTime X x D ω then
        (if riskProcess X x D T ω ∈ Icc (0 : ℝ) B then
          w (riskProcess X x D T ω) else 0) else 0) :=
    Measurable.ite hSurvival hPiece measurable_const
  have hEq :
      (fun ω => if (T : ℝ≥0∞) < ruinTime X x D ω then
        w (riskProcess X x D T ω) else 0) =
      (fun ω => if (T : ℝ≥0∞) < ruinTime X x D ω then
        (if riskProcess X x D T ω ∈ Icc (0 : ℝ) B then
          w (riskProcess X x D T ω) else 0) else 0) := by
    funext ω
    by_cases h : (T : ℝ≥0∞) < ruinTime X x D ω
    · have hCap := capped_surviving_riskProcess_range_real_finite
        X x B hx hB hxc D hD ω T h
      simp only [if_pos h, if_pos hCap]
    · simp only [if_neg h]
  have hMeas : AEStronglyMeasurable
      (fun ω => if (T : ℝ≥0∞) < ruinTime X x D ω then
        w (riskProcess X x D T ω) else 0) P := by
    rw [hEq]
    exact hTerminal.aestronglyMeasurable
  exact capped_surviving_terminal_test_integrable_of_measurable
    X w hw B hB x hx hxc D hD (fun _ => T) hMeas
