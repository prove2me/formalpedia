-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB126_native_joint_centered_drifted_tube_of_measurable_lift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:35:56.137953+00:00
-- url     : https://prove2.me/submissions/6baf91b0-7f0c-4ff4-a2bb-e4f9c5cae24a

import Mathlib
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Definitions.Def_GlynnSTS_Limit_Setting
import Theorems.Thm_AvramDividend_Classical_avram_gbB125_joint_centered_and_drifted_brownian_overshoot_tube_positive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- A measurable continuous Brownian lift transfers the overshoot-safe source tube support. -/
theorem solution
  [IsProbabilityMeasure gaussianLimit]
  (W : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
  (hW : IsBrownianReal W gaussianLimit)
  (B : (ℝ≥0 → ℝ) → C(unitInterval, ℝ))
  (hMeas : Measurable B)
  (hCoord : ∀ ω (t : unitInterval), B ω t = W ⟨t, t.2.1⟩ ω)
  (t : unitInterval) (ht : (t : ℝ) = (17 / 16000 : ℝ)) :
  0 < gaussianLimit {ω | ∀ s : unitInterval, s ≤ t →
    |W ⟨s, s.2.1⟩ ω| < (1 / 4000 : ℝ) ∧
      |W ⟨s, s.2.1⟩ ω + 2 * (s : ℝ)| < (1 / 400 : ℝ)} := by
  have hStd : GlynnSTS.Limit.IsStdBMC gaussianLimit B := by
    exact ⟨hMeas, W, hW, hCoord⟩
  have hPos :=
    avram_gbB125_joint_centered_and_drifted_brownian_overshoot_tube_positive
      gaussianLimit B hStd t ht
  have hEq :
      {ω | ∀ s : unitInterval, s ≤ t →
        |B ω s| < (1 / 4000 : ℝ) ∧
        |B ω s + 2 * (s : ℝ)| < (1 / 400 : ℝ)} =
      {ω | ∀ s : unitInterval, s ≤ t →
        |W ⟨s, s.2.1⟩ ω| < (1 / 4000 : ℝ) ∧
      |W ⟨s, s.2.1⟩ ω + 2 * (s : ℝ)| < (1 / 400 : ℝ)} := by
    ext ω
    simp [hCoord]
  simpa only [hEq] using hPos
