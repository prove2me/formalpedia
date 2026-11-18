-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB125_joint_centered_and_drifted_brownian_overshoot_tube_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:30:44.035261+00:00
-- url     : https://prove2.me/submissions/afe94526-83b5-418d-8f08-80beb199d065

import Mathlib
import Definitions.Def_GlynnSTS_NoAttain_Setting
import Theorems.Thm_GlynnSTS_NoAttain_small_ball_positive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section
/-- One Brownian small-ball event controls reserve drift and all centred meshes. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (B : Ω → C(unitInterval, ℝ))
  (hB : GlynnSTS.Limit.IsStdBMC P B)
  (t : unitInterval) (ht : (t : ℝ) = (17 / 16000 : ℝ)) :
  0 < P {ω | ∀ s : unitInterval, s ≤ t →
    |B ω s| < (1 / 4000 : ℝ) ∧
    |B ω s + 2 * (s : ℝ)| < (1 / 400 : ℝ)} := by
  have hSmall := GlynnSTS.NoAttain.small_ball_positive P B hB t
    (1 / 8000 : ℝ) (0 : ℝ) (by norm_num)
  have hSub :
      {ω | |B ω t - (0 : ℝ)| < (1 / 8000 : ℝ) ∧
        ∀ s : unitInterval, s ≤ t → |B ω s| < 2 * (1 / 8000 : ℝ)} ⊆
      {ω | ∀ s : unitInterval, s ≤ t →
        |B ω s| < (1 / 4000 : ℝ) ∧
        |B ω s + 2 * (s : ℝ)| < (1 / 400 : ℝ)} := by
    intro ω hω s hs
    have hBsmall := hω.2 s hs
    have hcenter : |B ω s| < (1 / 4000 : ℝ) := by
      convert hBsmall using 1 <;> norm_num
    constructor
    · exact hcenter
    · have hsle : (s : ℝ) ≤ (17 / 16000 : ℝ) := by
        have hst : (s : ℝ) ≤ (t : ℝ) := hs
        linarith
      have hpos : 0 ≤ 2 * (s : ℝ) :=
        mul_nonneg (by norm_num) s.property.1
      have hTri := abs_add_le (B ω s) (2 * (s : ℝ))
      rw [abs_of_nonneg hpos] at hTri
      nlinarith
  exact lt_of_lt_of_le hSmall (measure_mono hSub)
