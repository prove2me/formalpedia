-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_positive_long_centered_brownian_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T21:42:43.825202+00:00
-- url     : https://prove2.me/submissions/b04ada42-ed9b-43d4-9c9d-9a4af2bc444c

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_GlynnSTS_NoAttain_Setting
import Theorems.Thm_GlynnSTS_NoAttain_small_ball_positive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section
/-- Positive probability of a longer centred Brownian tube. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ))
    (hB : GlynnSTS.Limit.IsStdBMC P B) :
    0 < P {ω | ∀ s : unitInterval,
      s ≤ (⟨(1 / 500 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
      |B ω s| < (1 / 4000 : ℝ)} := by
  let t : unitInterval := ⟨(1 / 500 : ℝ), by constructor <;> norm_num⟩
  have hSmall := GlynnSTS.NoAttain.small_ball_positive P B hB t
    (1 / 16000 : ℝ) (0 : ℝ) (by norm_num)
  have hSub :
      {ω | |B ω t - (0 : ℝ)| < (1 / 16000 : ℝ) ∧
        ∀ s : unitInterval, s ≤ t → |B ω s| < 2 * (1 / 16000 : ℝ)} ⊆
      {ω | ∀ s : unitInterval, s ≤ t →
        |B ω s| < (1 / 4000 : ℝ)} := by
    intro ω hω s hs
    have hBsmall := hω.2 s hs
    nlinarith
  exact lt_of_lt_of_le hSmall (measure_mono hSub)
