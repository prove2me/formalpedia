-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_long_mesh_source_tube_of_native_joint_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:02:28.10184+00:00
-- url     : https://prove2.me/submissions/f6a6b715-d39b-4dc3-a2c1-644ee843486e

import Mathlib.Tactic.NormNum
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_unitInterval_long_tube_uniform_nnreal_lemma
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Source-faithful long Brownian tube through original stopped G/H mesh overshoot. -/
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
    ∀ ω ∈ E, ∀ t : ℝ≥0, t ≤ (17 / 16000 : ℝ≥0) →
      Y.X t ω = (brownian t ω - brownian 0 ω) + 2 * (t : ℝ) ∧
      |brownian t ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
      |Y.X t ω| ≤ (1 / 400 : ℝ) := by
  intro ω hω t ht
  have hCentered : ∀ t : ℝ≥0,
      t ≤ (17 / 16000 : ℝ≥0) →
      |brownian t ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) := by
    apply avram_gaussianB_unitInterval_long_tube_uniform_nnreal_lemma
    intro s hs
    exact (hTube ω hω s hs).1
  have hDrifted : ∀ t : ℝ≥0,
      t ≤ (17 / 16000 : ℝ≥0) →
      |brownian t ω - brownian 0 ω + 2 * (t : ℝ)| ≤
        (1 / 400 : ℝ) := by
    apply avram_gaussianB_unitInterval_long_tube_uniform_nnreal_lemma
    intro s hs
    exact (hTube ω hω s hs).2
  refine ⟨hpath t ω, hCentered t ht, ?_⟩
  calc
    |Y.X t ω| =
        |brownian t ω - brownian 0 ω + 2 * (t : ℝ)| :=
      congrArg abs (hpath t ω)
    _ ≤ (1 / 400 : ℝ) := hDrifted t ht
