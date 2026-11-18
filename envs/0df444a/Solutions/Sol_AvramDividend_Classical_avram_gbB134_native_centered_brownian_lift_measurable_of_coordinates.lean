-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB134_native_centered_brownian_lift_measurable_of_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T19:14:38.469199+00:00
-- url     : https://prove2.me/submissions/234c9993-27d3-4cff-861b-31b50b9f01b0

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting
import Theorems.Thm_AvramDividend_Classical_avram_gbB44_native_brownian_centered_continuous_path_lift
import Theorems.Thm_AvramDividend_Classical_avram_gbMeas5_native_continuousPath_measurable_bernstein
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped unitInterval NNReal ENNReal
noncomputable section
/-- Native canonical Brownian continuous-path lift is measurable from coordinates. -/
theorem solution
    (hCoordMeas : ∀ t : ℝ≥0,
      Measurable (fun ω : ℝ≥0 → ℝ =>
        ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω)) :
    ∃ B : (ℝ≥0 → ℝ) → C(unitInterval, ℝ),
      Measurable B ∧
      ∀ (ω : ℝ≥0 → ℝ) (t : unitInterval),
        B ω t = ProbabilityTheory.brownian
          (⟨(t : ℝ), t.2.1⟩ : ℝ≥0) ω -
          ProbabilityTheory.brownian 0 ω := by
  obtain ⟨B, hCoord⟩ :=
    avram_gbB44_native_brownian_centered_continuous_path_lift
  refine ⟨B, ?_, hCoord⟩
  apply avram_gbMeas5_native_continuousPath_measurable_bernstein
  intro t
  have h : Measurable (fun ω : ℝ≥0 → ℝ =>
      ProbabilityTheory.brownian
        (⟨(t : ℝ), t.2.1⟩ : ℝ≥0) ω -
        ProbabilityTheory.brownian 0 ω) :=
    hCoordMeas ⟨(t : ℝ), t.2.1⟩
  simpa only [hCoord] using h
