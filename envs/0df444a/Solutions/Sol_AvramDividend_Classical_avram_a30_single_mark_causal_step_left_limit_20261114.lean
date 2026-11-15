-- Prove2me | solution 1 for AvramDividend.Classical.avram_a30_single_mark_causal_step_left_limit_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:27:24.610837+00:00
-- url     : https://prove2.me/submissions/efe116de-ab63-43b6-bf35-ef3343ca42c2

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- An individual causal marked-jump step has its exact pre-jump left limit. -/
theorem solution (u : ℝ≥0) (a : ℝ) :
    ∀ t : ℝ≥0, 0 < t →
      Tendsto (fun v : ℝ≥0 => if u ≤ v then a else 0)
        (𝓝[<] t) (𝓝 (if u < t then a else 0)) := by
  intro t ht
  by_cases hut : u < t
  · have he : (fun v : ℝ≥0 => if u ≤ v then a else 0) =ᶠ[𝓝[<] t]
        (fun _ => a) := by
      have hgt : ∀ᶠ v : ℝ≥0 in 𝓝[<] t, u < v :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hut)
      filter_upwards [hgt] with v hv
      simp [le_of_lt hv]
    rw [if_pos hut]
    exact tendsto_const_nhds.congr' he.symm
  · have htu : t ≤ u := le_of_not_gt hut
    have he : (fun v : ℝ≥0 => if u ≤ v then a else 0) =ᶠ[𝓝[<] t]
        (fun _ => (0 : ℝ)) := by
      have hlt : ∀ᶠ v : ℝ≥0 in 𝓝[<] t, v < t :=
        self_mem_nhdsWithin
      filter_upwards [hlt] with v hv
      simp [not_le.mpr (lt_of_lt_of_le hv htu)]
    rw [if_neg hut]
    exact tendsto_const_nhds.congr' he.symm
