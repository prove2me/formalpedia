-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB167_native_positive_centered_brownian_short_tube_of_measurable_lift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T21:01:40.212415+00:00
-- url     : https://prove2.me/submissions/3791eb72-f706-491e-a91c-d68f0599c3ee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB126_native_joint_centered_drifted_tube_of_measurable_lift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Native positive Gaussian small-ball event at the shorter exact horizon. -/
theorem solution
    [IsProbabilityMeasure gaussianLimit]
    (W : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hW : IsBrownianReal W gaussianLimit)
    (B : (ℝ≥0 → ℝ) → C(unitInterval, ℝ))
    (hMeas : Measurable B)
    (hCoord : ∀ ω (t : unitInterval), B ω t = W ⟨t, t.2.1⟩ ω) :
    0 < gaussianLimit {ω | ∀ s : unitInterval,
      s ≤ (⟨(1 / 1000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
      |W ⟨s, s.2.1⟩ ω| < (1 / 4000 : ℝ)} := by
  let tLarge : unitInterval :=
    ⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩
  let tSmall : unitInterval :=
    ⟨(1 / 1000 : ℝ), by constructor <;> norm_num⟩
  have hTS : tSmall ≤ tLarge := by
    change (1 / 1000 : ℝ) ≤ (17 / 16000 : ℝ)
    norm_num
  have hLarge :
      0 < gaussianLimit {ω | ∀ s : unitInterval, s ≤ tLarge →
        |W ⟨s, s.2.1⟩ ω| < (1 / 4000 : ℝ) ∧
        |W ⟨s, s.2.1⟩ ω + 2 * (s : ℝ)| < (1 / 400 : ℝ)} :=
    avram_gbB126_native_joint_centered_drifted_tube_of_measurable_lift
      W hW B hMeas hCoord tLarge (by rfl)
  have hSub :
      {ω | ∀ s : unitInterval, s ≤ tLarge →
        |W ⟨s, s.2.1⟩ ω| < (1 / 4000 : ℝ) ∧
        |W ⟨s, s.2.1⟩ ω + 2 * (s : ℝ)| < (1 / 400 : ℝ)} ⊆
      {ω | ∀ s : unitInterval, s ≤ tSmall →
        |W ⟨s, s.2.1⟩ ω| < (1 / 4000 : ℝ)} := by
    intro ω hω s hs
    exact (hω s (hs.trans hTS)).1
  exact lt_of_lt_of_le hLarge (measure_mono hSub)
