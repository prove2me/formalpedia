-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB107_native_overshoot_safe_brownian_tube_of_measurable_lift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:16:33.368604+00:00
-- url     : https://prove2.me/submissions/e1081151-6642-4412-bb8e-9c4c3ffffb62

import Mathlib
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Definitions.Def_GlynnSTS_Limit_Setting
import Theorems.Thm_AvramDividend_Classical_avram_gbB106_overshoot_safe_drifted_brownian_tube
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
    |W ⟨s, s.2.1⟩ ω + 2 * (s : ℝ)| < (1 / 400 : ℝ)} := by
  have hStd : GlynnSTS.Limit.IsStdBMC gaussianLimit B := by
    exact ⟨hMeas, W, hW, hCoord⟩
  have hPos :=
    avram_gbB106_overshoot_safe_drifted_brownian_tube
      gaussianLimit B hStd t ht
  have hEq :
      {ω | ∀ s : unitInterval, s ≤ t →
        |B ω s + 2 * (s : ℝ)| < (1 / 400 : ℝ)} =
      {ω | ∀ s : unitInterval, s ≤ t →
        |W ⟨s, s.2.1⟩ ω + 2 * (s : ℝ)| < (1 / 400 : ℝ)} := by
    ext ω
    simp [hCoord]
  simpa only [hEq] using hPos
