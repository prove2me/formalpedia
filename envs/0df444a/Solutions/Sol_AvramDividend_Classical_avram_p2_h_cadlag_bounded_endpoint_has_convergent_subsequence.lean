-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_bounded_endpoint_has_convergent_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:01:47.80292+00:00
-- url     : https://prove2.me/submissions/451463e6-4314-4069-a2dc-2f315fc8d3c8

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- A bounded sequence of candidate grid endpoints admits a strictly
increasing convergent subsequence in the closed compact horizon. -/
theorem solution
    (T : ℝ≥0) (b : ℕ → ℝ≥0)
    (hb : ∀ n, b n ≤ T) :
    ∃ t : ℝ≥0, t ≤ T ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (b ∘ φ) atTop (𝓝 t) := by
  have hmem : ∀ n, b n ∈ Set.Icc (0 : ℝ≥0) T := by
    intro n
    exact ⟨(show (0 : ℝ≥0) ≤ b n from zero_le), hb n⟩
  obtain ⟨t, ht, φ, hφ, hlim⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) T)).tendsto_subseq hmem
  exact ⟨t, ht.2, φ, hφ, hlim⟩
