-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB185_native_centered_brownian_joint_long_tube_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T19:18:23.355261+00:00
-- url     : https://prove2.me/submissions/b63390d2-b4c9-4c00-a19d-5bde9fb3d585

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting
import Theorems.Thm_AvramDividend_Classical_avram_gbB134_native_centered_brownian_lift_measurable_of_coordinates
import Theorems.Thm_AvramDividend_Classical_avram_gbB135_native_centered_brownian_coordinate_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB126_native_joint_centered_drifted_tube_of_measurable_lift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Native centered canonical Brownian joint long tube has positive probability. -/
theorem solution
    [IsProbabilityMeasure gaussianLimit]
    (hW : IsBrownianReal (fun t : ℝ≥0 => fun ω : ℝ≥0 → ℝ =>
      ProbabilityTheory.brownian t ω -
        ProbabilityTheory.brownian 0 ω) gaussianLimit) :
    0 < gaussianLimit {ω : ℝ≥0 → ℝ |
      ∀ s : unitInterval, s ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
        |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω -
            ProbabilityTheory.brownian 0 ω| < (1 / 4000 : ℝ) ∧
        |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω -
            ProbabilityTheory.brownian 0 ω +
            2 * (s : ℝ)| < (1 / 400 : ℝ)} := by
  obtain ⟨B, hMeas, hCoord⟩ :=
    avram_gbB134_native_centered_brownian_lift_measurable_of_coordinates
      avram_gbB135_native_centered_brownian_coordinate_measurable
  have hPos :=
    avram_gbB126_native_joint_centered_drifted_tube_of_measurable_lift
      (fun t : ℝ≥0 => fun ω : ℝ≥0 → ℝ =>
      ProbabilityTheory.brownian t ω -
        ProbabilityTheory.brownian 0 ω)
      hW B hMeas hCoord (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) rfl
  simpa only using hPos
