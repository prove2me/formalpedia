-- Prove2me | solution 1 for AvramDividend.Classical.avram_a51_continuous_real_path_has_allpath_cadlag_no_positive_jumps_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:07:28.689169+00:00
-- url     : https://prove2.me/submissions/0fe61099-cdf3-41a5-a826-5a88dc7a320e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Every continuous real path on nonnegative time has no positive left jumps. -/
theorem solution
    (f : ℝ≥0 → ℝ) (hf : Continuous f) :
    (∀ t : ℝ≥0, ContinuousWithinAt f (Ici t) t) ∧
    (∀ t : ℝ≥0, 0 < t →
      ∃ l, Tendsto f (𝓝[<] t) (𝓝 l)) ∧
    (∀ t l, 0 < t →
      Tendsto f (𝓝[<] t) (𝓝 l) → f t ≤ l) := by
  constructor
  · intro t
    exact (hf.continuousAt).continuousWithinAt
  constructor
  · intro t ht
    refine ⟨f t, ?_⟩
    exact (hf.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  · intro t l ht hl
    have hCont : Tendsto f (𝓝[<] t) (𝓝 (f t)) :=
      (hf.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    haveI : NeBot (𝓝[<] t) :=
      nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    have heq : l = f t := tendsto_nhds_unique hl hCont
    rw [heq]
