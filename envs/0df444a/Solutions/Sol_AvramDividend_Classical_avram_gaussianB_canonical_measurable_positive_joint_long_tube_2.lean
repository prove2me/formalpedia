-- Prove2me | solution 2 for AvramDividend.Classical.avram_gaussianB_canonical_measurable_positive_joint_long_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:46:11.157139+00:00
-- url     : https://prove2.me/submissions/a5959353-557b-4dbf-b817-103aa3209f91

import Mathlib.Tactic.NormNum
import Definitions.Def_GlynnSTS_Limit_Setting
import Theorems.Thm_AvramDividend_Classical_avram_gbB134_native_centered_brownian_lift_measurable_of_coordinates
import Theorems.Thm_AvramDividend_Classical_avram_gbB135_native_centered_brownian_coordinate_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB186_canonical_gaussian_centered_joint_long_tube_positive_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_joint_closed_continuous_path_tube_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Authentic canonical measurable positive Brownian tube event. -/
theorem solution
    [IsProbabilityMeasure gaussianLimit] :
    ∃ E : Set (ℝ≥0 → ℝ),
      MeasurableSet E ∧ 0 < gaussianLimit E ∧
      (∀ ω ∈ E, ∀ s : unitInterval, s ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
        |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω - ProbabilityTheory.brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
        |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω - ProbabilityTheory.brownian 0 ω + 2 * (s : ℝ)| ≤ (1 / 400 : ℝ)) := by
  let T : unitInterval := (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval)
  let E : Set (ℝ≥0 → ℝ) :=
    {ω | ∀ s : unitInterval, s ≤ T →
      |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω - ProbabilityTheory.brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
      |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω - ProbabilityTheory.brownian 0 ω + 2 * (s : ℝ)| ≤ (1 / 400 : ℝ)}
  obtain ⟨B, hMeas, hCoord⟩ :=
    avram_gbB134_native_centered_brownian_lift_measurable_of_coordinates
      avram_gbB135_native_centered_brownian_coordinate_measurable
  have hBMeas : MeasurableSet
      {ω : ℝ≥0 → ℝ | ∀ s : unitInterval, s ≤ T →
        |B ω s| ≤ (1 / 4000 : ℝ) ∧
        |B ω s + 2 * (s : ℝ)| ≤ (1 / 400 : ℝ)} :=
    avram_gaussianB_joint_closed_continuous_path_tube_measurable
      B hMeas T (1 / 4000 : ℝ) (1 / 400 : ℝ)
  have hEeq : E =
      {ω : ℝ≥0 → ℝ | ∀ s : unitInterval, s ≤ T →
        |B ω s| ≤ (1 / 4000 : ℝ) ∧
        |B ω s + 2 * (s : ℝ)| ≤ (1 / 400 : ℝ)} := by
    ext ω
    simp [E, hCoord]
  have hEmeas : MeasurableSet E := by
    rw [hEeq]
    exact hBMeas
  have hPosStrict :=
    avram_gbB186_canonical_gaussian_centered_joint_long_tube_positive_unconditional
  have hSub :
      {ω : ℝ≥0 → ℝ | ∀ s : unitInterval, s ≤ T →
        |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω - ProbabilityTheory.brownian 0 ω| < (1 / 4000 : ℝ) ∧
        |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω - ProbabilityTheory.brownian 0 ω + 2 * (s : ℝ)| < (1 / 400 : ℝ)} ⊆ E := by
    intro ω hω
    change ∀ s : unitInterval, s ≤ T →
      |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω - ProbabilityTheory.brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
      |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω - ProbabilityTheory.brownian 0 ω + 2 * (s : ℝ)| ≤ (1 / 400 : ℝ)
    intro s hs
    exact ⟨(hω s hs).1.le, (hω s hs).2.le⟩
  have hPos : 0 < gaussianLimit E :=
    lt_of_lt_of_le hPosStrict (measure_mono hSub)
  refine ⟨E, hEmeas, hPos, ?_⟩
  intro ω hω s hs
  exact hω s hs
