-- Prove2me | solution 2 for AvramDividend.Classical.avram_gbB134_native_centered_brownian_lift_measurable_of_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T19:14:50.938145+00:00
-- url     : https://prove2.me/submissions/c36ff011-98ce-47d5-9f5a-8471501d9b50

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting
import Theorems.Thm_AvramDividend_Classical_avram_gbMeas5_native_continuousPath_measurable_bernstein
import Theorems.Thm_AvramDividend_Classical_avram_gbB44_native_brownian_centered_continuous_path_lift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- A native Brownian continuous path lift is measurable from coordinate measurability. -/
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
  obtain ⟨B, hB⟩ :=
    avram_gbB44_native_brownian_centered_continuous_path_lift
  refine ⟨B, ?_, hB⟩
  apply avram_gbMeas5_native_continuousPath_measurable_bernstein
  intro t
  have heq : (fun ω : ℝ≥0 → ℝ => B ω t) =
      (fun ω : ℝ≥0 → ℝ =>
        ProbabilityTheory.brownian
          (⟨(t : ℝ), t.2.1⟩ : ℝ≥0) ω -
          ProbabilityTheory.brownian 0 ω) := by
    funext ω
    exact hB ω t
  rw [heq]
  exact hCoordMeas (⟨(t : ℝ), t.2.1⟩ : ℝ≥0)
