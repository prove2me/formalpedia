-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_radial_left_inverse_tangent
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:17:37.305416+00:00
-- url     : https://prove2.me/submissions/9d6f63ba-baef-420f-a870-f23615b153e4

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u w : Phase) (hu : u ∈ unitThreeSphere)
    (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    fderiv ℝ radialNormalize (G u) (fderiv ℝ G u w) = w := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.2.2.2.2.1
