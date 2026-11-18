-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_native_joint_long_tube_bounds_all_short_nonnegative_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:04:42.708916+00:00
-- url     : https://prove2.me/submissions/8e5bf47c-48ee-4a09-bb5d-1bb894ff4cdf

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal
noncomputable section
/-- Reuse accepted generic time embedding for both native Brownian tube components. -/
theorem solution
    (ω : ℝ≥0 → ℝ)
    (hTube : ∀ s : unitInterval,
      s ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
      |brownian ⟨s, s.2.1⟩ ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
      |brownian ⟨s, s.2.1⟩ ω - brownian 0 ω +
        2 * (s : ℝ)| ≤ (1 / 400 : ℝ)) :
    ∀ t : ℝ≥0, t ≤ (1 / 1000 : ℝ≥0) →
      |brownian t ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
      |brownian t ω - brownian 0 ω +
        2 * (t : ℝ)| ≤ (1 / 400 : ℝ) := by
  have hCenter : ∀ t : ℝ≥0,
      t ≤ (1 / 1000 : ℝ≥0) →
      |brownian t ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) := by
    apply avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
    intro u hu
    exact (hTube u hu).1
  have hDrift : ∀ t : ℝ≥0,
      t ≤ (1 / 1000 : ℝ≥0) →
      |brownian t ω - brownian 0 ω + 2 * (t : ℝ)| ≤
        (1 / 400 : ℝ) := by
    apply avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
    intro u hu
    exact (hTube u hu).2
  intro t ht
  exact ⟨hCenter t ht, hDrift t ht⟩
