-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_canonical_measurable_positive_joint_long_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:45:49.254712+00:00
-- url     : https://prove2.me/submissions/a6975e7b-9834-42c9-beb7-f057068f2a23

import Mathlib
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

theorem solution
    [IsProbabilityMeasure gaussianLimit] :
    ∃ E : Set (ℝ≥0 → ℝ),
      MeasurableSet E ∧ 0 < gaussianLimit E ∧
      (∀ ω ∈ E, ∀ s : unitInterval, s ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
        |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω - ProbabilityTheory.brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
        |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω - ProbabilityTheory.brownian 0 ω + 2 * (s : ℝ)| ≤ (1 / 400 : ℝ)) := by 
  obtain ⟨B, hBM, hCoord⟩ :=
    avram_gbB134_native_centered_brownian_lift_measurable_of_coordinates
      avram_gbB135_native_centered_brownian_coordinate_measurable
  let T : unitInterval := ⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩
  let E : Set (ℝ≥0 → ℝ) := {ω | ∀ s : unitInterval, s ≤ T →
    |B ω s| ≤ (1 / 4000 : ℝ) ∧
    |B ω s + 2 * (s : ℝ)| ≤ (1 / 400 : ℝ)}
  have hMeas : MeasurableSet E :=
    avram_gaussianB_joint_closed_continuous_path_tube_measurable
      B hBM T (1 / 4000 : ℝ) (1 / 400 : ℝ)
  have hSub :
      {ω : ℝ≥0 → ℝ | ∀ s : unitInterval, s ≤ T →
        |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω -
          ProbabilityTheory.brownian 0 ω| < (1 / 4000 : ℝ) ∧
        |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω -
          ProbabilityTheory.brownian 0 ω + 2 * (s : ℝ)| < (1 / 400 : ℝ)} ⊆ E := by
    intro ω hω
    intro s hs
    change |B ω s| ≤ (1 / 4000 : ℝ) ∧
      |B ω s + 2 * (s : ℝ)| ≤ (1 / 400 : ℝ)
    rw [hCoord ω s]
    exact ⟨(hω s hs).1.le, (hω s hs).2.le⟩
  have hPos : 0 < gaussianLimit E :=
    lt_of_lt_of_le
      avram_gbB186_canonical_gaussian_centered_joint_long_tube_positive_unconditional
      (measure_mono hSub)
  refine ⟨E, hMeas, hPos, ?_⟩
  intro ω hω s hs
  have h := hω s hs
  simpa only [hCoord] using h
