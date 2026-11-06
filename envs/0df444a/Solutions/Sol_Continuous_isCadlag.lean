-- Prove2me | solution 1 for Continuous.isCadlag
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:11:12.060177+00:00
-- url     : https://prove2.me/submissions/6d2558c2-6836-4c43-914b-d5065eb4a1a1

import Definitions.Def_LeanLevy_Processes_Cadlag
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Set Topology ProbabilityTheory
universe u₁ u₂

theorem solution {α : Type u₁} {β : Type u₂}
    [TopologicalSpace α] [TopologicalSpace β] [Preorder α]
    {f : α → β} (hf : Continuous f) : IsCadlag f := by
  intro t
  exact ⟨hf.continuousWithinAt, f t, (hf.tendsto t).mono_left nhdsWithin_le_nhds⟩
