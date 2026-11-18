-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbWill_20261117_native_centered_short_event_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T21:09:49.00825+00:00
-- url     : https://prove2.me/submissions/2511fb19-6557-4025-9f09-05db8b209793

import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_GlynnSTS_Limit_Setting
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Theorems.Thm_AvramDividend_Classical_avram_gbB134_native_centered_brownian_lift_measurable_of_coordinates
import Theorems.Thm_AvramDividend_Classical_avram_gbB135_native_centered_brownian_coordinate_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB167_native_positive_centered_brownian_short_tube_of_measurable_lift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Canonical native centered Gaussian tube has strictly positive probability. -/
theorem solution
    [IsProbabilityMeasure gaussianLimit] :
    0 < gaussianLimit {ω : ℝ≥0 → ℝ |
      ∀ s : unitInterval,
        s ≤ (⟨(1 / 1000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
        |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω -
          ProbabilityTheory.brownian 0 ω| < (1 / 4000 : ℝ)} := by
  obtain ⟨B, hMeas, hCoord⟩ :=
    avram_gbB134_native_centered_brownian_lift_measurable_of_coordinates
      avram_gbB135_native_centered_brownian_coordinate_measurable
  have hStd : IsBrownianReal
      (fun t : ℝ≥0 => fun ω : ℝ≥0 → ℝ =>
        ProbabilityTheory.brownian t ω -
          ProbabilityTheory.brownian 0 ω) gaussianLimit := by
    simpa only [zero_add] using
      (ProbabilityTheory.isBrownianReal_brownian_avram.shift 0)
  have hPos :=
    avram_gbB167_native_positive_centered_brownian_short_tube_of_measurable_lift
      (fun t : ℝ≥0 => fun ω : ℝ≥0 → ℝ =>
        ProbabilityTheory.brownian t ω -
          ProbabilityTheory.brownian 0 ω)
      hStd B hMeas hCoord
  simpa only using hPos
