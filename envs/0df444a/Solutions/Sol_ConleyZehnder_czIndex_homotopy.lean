-- Prove2me | solution 1 for ConleyZehnder.czIndex_homotopy
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T22:36:43.453884+00:00
-- url     : https://prove2.me/submissions/f778794b-c97c-4e99-88eb-b343be672cd8

import Theorems.Thm_ConleyZehnder_czIndex_locally_constant

open ConleyZehnder Filter Topology

theorem solution (n : ℕ) : HomotopyAxiom (czIndex (n := n)) := by
  intro ψ hψ ψ' hψ'
  have hc : ContinuousOn (czIndex (n := n)) (SP n) := by
    intro x hx
    show Tendsto czIndex (𝓝[SP n] x) (𝓝 (czIndex x))
    rw [nhds_discrete, tendsto_pure, eventually_nhdsWithin_iff]
    exact czIndex_locally_constant x hx
  exact isPreconnected_connectedComponentIn.constant
    (hc.mono (connectedComponentIn_subset _ _)) hψ' (mem_connectedComponentIn hψ)
