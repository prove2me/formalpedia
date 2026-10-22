-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_gauge_differential_energy_tangent
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:39:02.413658+00:00
-- url     : https://prove2.me/submissions/17930b13-a88a-4ce8-8404-6f10743e9144

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    fderiv ℝ M.modelHamiltonian (G u) (fderiv ℝ G u v) = 0 := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.1
