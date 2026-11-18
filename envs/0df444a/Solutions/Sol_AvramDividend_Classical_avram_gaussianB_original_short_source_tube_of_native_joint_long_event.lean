-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_short_source_tube_of_native_joint_long_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:02:41.336079+00:00
-- url     : https://prove2.me/submissions/8cbaff57-58f0-4927-aeb7-2096a2f4ed8d

import Mathlib.Tactic.NormNum
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.BrownianMotion.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- True original Gaussian source bounds via Proved exact unitInterval NNReal bridge. -/
theorem solution
    (𝓕 : Filtration ℝ≥0
      (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
    (Y : SpectrallyNegativeLevy gaussianLimit 𝓕)
    (hpath : ∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
      Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ))
    (E : Set (ℝ≥0 → ℝ))
    (hTube : ∀ ω ∈ E, ∀ s : unitInterval,
      s ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
      |brownian ⟨s, s.2.1⟩ ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
      |brownian ⟨s, s.2.1⟩ ω - brownian 0 ω +
        2 * (s : ℝ)| ≤ (1 / 400 : ℝ)) :
    ∀ ω ∈ E, ∀ t : ℝ≥0, t ≤ (1 / 1000 : ℝ≥0) →
      Y.X t ω = (brownian t ω - brownian 0 ω) + 2 * (t : ℝ) ∧
      |brownian t ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
      |Y.X t ω| ≤ (1 / 400 : ℝ) := by
  intro ω hω t ht
  have hC : ∀ u : ℝ≥0, u ≤ (1 / 1000 : ℝ≥0) →
      |brownian u ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) := by
    apply avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
    intro u hu
    exact (hTube ω hω u hu).1
  have hD : ∀ u : ℝ≥0, u ≤ (1 / 1000 : ℝ≥0) →
      |brownian u ω - brownian 0 ω + 2 * (u : ℝ)| ≤
        (1 / 400 : ℝ) := by
    apply avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
    intro u hu
    exact (hTube ω hω u hu).2
  refine ⟨hpath t ω, hC t ht, ?_⟩
  calc
    |Y.X t ω| =
        |brownian t ω - brownian 0 ω + 2 * (t : ℝ)| :=
      congrArg abs (hpath t ω)
    _ ≤ (1 / 400 : ℝ) := hD t ht
