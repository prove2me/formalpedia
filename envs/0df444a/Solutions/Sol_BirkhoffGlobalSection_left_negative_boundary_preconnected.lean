-- Prove2me | solution 1 for BirkhoffGlobalSection.left_negative_boundary_preconnected
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T17:18:25.02865+00:00
-- url     : https://prove2.me/submissions/b0d31343-e64a-4c47-897f-0d72dd16b855

import Theorems.Thm_BirkhoffGlobalSection_left_negative_boundary_radial_graph
import Theorems.Thm_BirkhoffGlobalSection_unit_three_sphere_subtype_preconnected
import Mathlib.Topology.Constructions

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    IsPreconnected
      {s : Phase | s ∈ closure
        (connectedComponentIn
          {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
            0 < secondCollisionDistanceSq t}
          (fun _ : Fin 4 => (0 : ℝ))) ∧
        leviCivitaHamiltonian μ c s = 0 ∧
        0 < secondCollisionDistanceSq s} := by
  obtain ⟨ρ, hρ, _, hboundary⟩ :=
    left_negative_boundary_radial_graph μ c hμ0 hμ1 hc
  let f : {x : Phase // x ∈ unitThreeSphere} → Phase :=
    fun x i => ρ x * (x : Phase) i
  have hf : Continuous f := by
    refine continuous_pi fun i => ?_
    exact hρ.mul ((continuous_apply i).comp continuous_subtype_val)
  have hconn : IsPreconnected (Set.range f) := by
    simpa only [Set.image_univ] using
      (unit_three_sphere_subtype_preconnected.image f hf.continuousOn)
  rw [hboundary]
  exact hconn
