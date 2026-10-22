-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_smooth_radial_chart
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T00:25:45.379404+00:00
-- url     : https://prove2.me/submissions/231cfc86-90e7-4f57-82ff-a2f57deb81a8

import Theorems.Thm_ConvexAnalysis_convex_frontier_radial_derivative_ne_zero
import Theorems.Thm_BirkhoffGlobalSection_smooth_radial_gauge_chart

open BirkhoffGlobalSection ConvexAnalysis Filter Set
open scoped ContDiff Topology

private theorem convex_model_radial_derivative_ne_zero {μ c : ℝ}
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

theorem solution {μ c : ℝ} (M : ConvexRegularizationModel μ c) :
    let G : Phase → Phase := fun u => (gauge M.body u)⁻¹ • u
    (∀ y ∈ frontier M.body,
      ContDiffAt ℝ ∞ radialNormalize y ∧ radialNormalize y ∈ unitThreeSphere ∧
        G (radialNormalize y) = y) ∧
    (∀ u ∈ unitThreeSphere,
      ContDiffAt ℝ ∞ G u ∧ G u ∈ frontier M.body ∧ radialNormalize (G u) = u) := by
  apply smooth_radial_gauge_chart M.body M.body_convex
    (mem_interior_iff_mem_nhds.mp M.origin_interior)
    (M.body_compact.isVonNBounded ℝ) M.modelHamiltonian M.model_zero
  · intro y hy
    have hyimage : y ∈ M.toModel '' leftEnergyComponent μ c := by
      rw [M.image_frontier]
      exact hy
    obtain ⟨s, hs, rfl⟩ := hyimage
    exact M.model_smooth.contDiffAt
      (M.target_open.mem_nhds (M.toModel_mapsTo (M.contains_component hs)))
  · exact convex_model_radial_derivative_ne_zero M
