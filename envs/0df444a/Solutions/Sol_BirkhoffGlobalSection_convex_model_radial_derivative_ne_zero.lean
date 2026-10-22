-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_radial_derivative_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:24:27.860549+00:00
-- url     : https://prove2.me/submissions/23fc9ad6-f720-46ab-b17e-b7934a5daa82

import Theorems.Thm_ConvexAnalysis_convex_frontier_radial_derivative_ne_zero
import Theorems.Thm_BirkhoffGlobalSection_smooth_radial_gauge_chart

open BirkhoffGlobalSection ConvexAnalysis Filter Set
open scoped ContDiff Topology


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) :
    ∀ y ∈ frontier M.body, fderiv ℝ M.modelHamiltonian y y ≠ 0 := by
  intro y hy
  have hytarget : y ∈ M.target := by
    have hyimage : y ∈ M.toModel '' leftEnergyComponent μ c := by
      rw [M.image_frontier]
      exact hy
    obtain ⟨s, hs, rfl⟩ := hyimage
    exact M.toModel_mapsTo (M.contains_component hs)
  exact convex_frontier_radial_derivative_ne_zero M.body M.body_compact M.body_convex
    M.origin_interior M.modelHamiltonian M.model_zero y hy
    (M.model_smooth.contDiffAt (M.target_open.mem_nhds hytarget)) (M.model_regular y hy)
