-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_radial_derivative_positive
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:08:24.598035+00:00
-- url     : https://prove2.me/submissions/ec679561-8950-4c89-884f-7fe91fefa43e

import Theorems.Thm_ConvexAnalysis_convex_frontier_radial_derivative_positive
import Definitions.Def_BirkhoffGlobalSection_TransverseHopf

open BirkhoffGlobalSection ConvexAnalysis Filter Set
open scoped ContDiff Topology


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) :
    ∀ y ∈ frontier M.body, 0 < fderiv ℝ M.modelHamiltonian y y := by
  intro y hy
  have hytarget : y ∈ M.target := by
    have hyimage : y ∈ M.toModel '' leftEnergyComponent μ c := by
      rw [M.image_frontier]
      exact hy
    obtain ⟨s, hs, rfl⟩ := hyimage
    exact M.toModel_mapsTo (M.contains_component hs)
  exact convex_frontier_radial_derivative_positive M.body M.body_compact M.body_convex
    M.origin_interior M.modelHamiltonian M.model_zero y hy
    (M.model_smooth.contDiffAt (M.target_open.mem_nhds hytarget)) (M.model_regular y hy)
    (M.model_hessian.2 y hy)
