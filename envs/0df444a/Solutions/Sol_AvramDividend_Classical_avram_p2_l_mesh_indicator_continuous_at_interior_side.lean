-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_indicator_continuous_at_interior_side
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:38:58.530449+00:00
-- url     : https://prove2.me/submissions/73779e88-9054-4c17-88f8-d90b4d9aad13

import Mathlib
-- CE 25589: auto targeted imports lost TopologicalSpace Real.
-- Preserve pinned full Mathlib when repairing this candidate.

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology

/-- A Borel indicator is locally continuous wherever membership is
locally constant, on either interior side of its boundary. -/
theorem solution (B : Set ℝ) (x : ℝ)
    (h : x ∈ interior B ∨ x ∈ interior (Bᶜ)) :
    ContinuousAt (B.indicator (fun _ : ℝ => (1 : ℝ))) x := by
  classical
  rcases h with hIn | hOut
  · have hx : x ∈ B := interior_subset hIn
    have hInterior : ∀ᶠ z in 𝓝 x, z ∈ interior B :=
      isOpen_interior.mem_nhds hIn
    have hB : ∀ᶠ z in 𝓝 x, z ∈ B := by
      filter_upwards [hInterior] with z hz
      exact interior_subset hz
    have heq : (B.indicator (fun _ : ℝ => (1 : ℝ))) =ᶠ[𝓝 x]
        (fun _ : ℝ => (1 : ℝ)) := by
      filter_upwards [hB] with z hz
      simp [Set.indicator, hz]
    have ht : Tendsto (fun _ : ℝ => (1 : ℝ))
        (𝓝 x) (𝓝 (1 : ℝ)) := tendsto_const_nhds
    simpa [ContinuousAt, Set.indicator, hx] using ht.congr' heq.symm
  · have hx : x ∉ B := interior_subset hOut
    have hExterior : ∀ᶠ z in 𝓝 x, z ∈ interior (Bᶜ) :=
      isOpen_interior.mem_nhds hOut
    have hB : ∀ᶠ z in 𝓝 x, z ∉ B := by
      filter_upwards [hExterior] with z hz
      exact interior_subset hz
    have heq : (B.indicator (fun _ : ℝ => (1 : ℝ))) =ᶠ[𝓝 x]
        (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hB] with z hz
      simp [Set.indicator, hz]
    have ht : Tendsto (fun _ : ℝ => (0 : ℝ))
        (𝓝 x) (𝓝 (0 : ℝ)) := tendsto_const_nhds
    simpa [ContinuousAt, Set.indicator, hx] using ht.congr' heq.symm
