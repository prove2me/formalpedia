-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB42_native_gaussian_brownian_tube_of_measurable_lift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T15:56:23.693247+00:00
-- url     : https://prove2.me/submissions/82c9e865-4aaa-4a6b-af81-093fd8ede69f

import Mathlib
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Definitions.Def_GlynnSTS_Limit_Setting
import Theorems.Thm_AvramDividend_Classical_avram_gbB37_positive_small_drifted_brownian_tube
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- A measurable continuous Brownian lift transfers strict tube support. -/
theorem solution
  [IsProbabilityMeasure gaussianLimit]
  (W : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
  (hW : IsBrownianReal W gaussianLimit)
  (B : (ℝ≥0 → ℝ) → C(unitInterval, ℝ))
  (hMeas : Measurable B)
  (hCoord : ∀ ω (t : unitInterval), B ω t = W ⟨t, t.2.1⟩ ω)
  (t : unitInterval) (ht : (t : ℝ) = (1 / 1000 : ℝ)) :
  0 < gaussianLimit {ω | ∀ s : unitInterval, s ≤ t →
    |W ⟨s, s.2.1⟩ ω + 2 * (s : ℝ)| < (1 / 400 : ℝ)} := by
  have hStd : GlynnSTS.Limit.IsStdBMC gaussianLimit B := by
    exact ⟨hMeas, W, hW, hCoord⟩
  have hPos :=
    avram_gbB37_positive_small_drifted_brownian_tube
      gaussianLimit B hStd t ht
  have hEq :
      {ω | ∀ s : unitInterval, s ≤ t →
        |B ω s + 2 * (s : ℝ)| < (1 / 400 : ℝ)} =
      {ω | ∀ s : unitInterval, s ≤ t →
        |W ⟨s, s.2.1⟩ ω + 2 * (s : ℝ)| < (1 / 400 : ℝ)} := by
    ext ω
    simp [hCoord]
  simpa only [hEq] using hPos
