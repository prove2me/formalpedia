-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_frame_area_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:51.855969+00:00
-- url     : https://prove2.me/submissions/17b7d676-8943-4305-b0e3-2d98037494ca

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere)
    (p r : Plane),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    let A := convexModelSymplecticContactFrame M u 0
    let B := convexModelSymplecticContactFrame M u 1
    (-phaseSymplecticForm (fderiv ℝ G u (p 0 • A + p 1 • B))
      (fderiv ℝ G u (r 0 • A + r 1 • B))) = p 0 * r 1 - p 1 * r 0 := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.2.2.2.2.2.2.2.1
