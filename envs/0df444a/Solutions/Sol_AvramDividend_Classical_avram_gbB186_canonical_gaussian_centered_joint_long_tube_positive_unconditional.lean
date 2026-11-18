-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB186_canonical_gaussian_centered_joint_long_tube_positive_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T21:04:18.343269+00:00
-- url     : https://prove2.me/submissions/fa42f007-4c39-4d10-b549-c02ad24238f0

import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_GlynnSTS_Limit_Setting
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Theorems.Thm_AvramDividend_Classical_avram_gbB185_native_centered_brownian_joint_long_tube_positive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Unconditional native joint Gaussian tube from the Brownian shift. -/
theorem solution
    [IsProbabilityMeasure gaussianLimit] :
    0 < gaussianLimit {ω : ℝ≥0 → ℝ |
      ∀ s : unitInterval, s ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
        |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω -
            ProbabilityTheory.brownian 0 ω| < (1 / 4000 : ℝ) ∧
        |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω -
            ProbabilityTheory.brownian 0 ω +
            2 * (s : ℝ)| < (1 / 400 : ℝ)}  := by
  have hStd : IsBrownianReal
      (fun t : ℝ≥0 => fun ω : ℝ≥0 → ℝ =>
        ProbabilityTheory.brownian t ω -
          ProbabilityTheory.brownian 0 ω) gaussianLimit := by
    simpa only [zero_add] using
      (ProbabilityTheory.isBrownianReal_brownian_avram.shift 0)
  exact
    avram_gbB185_native_centered_brownian_joint_long_tube_positive hStd
