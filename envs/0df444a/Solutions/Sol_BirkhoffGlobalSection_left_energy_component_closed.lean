-- Prove2me | solution 1 for BirkhoffGlobalSection.left_energy_component_closed
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T18:31:32.803821+00:00
-- url     : https://prove2.me/submissions/064805ad-9951-4663-a17e-20c5c2a1bde7

import Mathlib.Topology.Connected.Basic
import Theorems.Thm_BirkhoffGlobalSection_left_component_closure_avoids_second_collision
import Theorems.Thm_BirkhoffGlobalSection_left_component_closure_energy_zero

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    IsClosed (leftEnergyComponent μ c) := by
  let F := regularEnergyLocus μ c
  let C := leftEnergyComponent μ c
  change IsClosed C
  have hclosure : closure C ⊆ F := by
    intro s hs
    exact ⟨left_component_closure_energy_zero μ c hμ0 hμ1 hc s hs,
      left_component_closure_avoids_second_collision μ c hμ0 hμ1 hc s hs⟩
  by_cases hx : leftCollisionPoint μ ∈ F
  · apply closure_subset_iff_isClosed.mp
    exact (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx)) hclosure
  · have he : C = ∅ := connectedComponentIn_eq_empty hx
    rw [he]
    exact isClosed_empty
