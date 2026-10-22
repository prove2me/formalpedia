-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_sphere_weight_regular
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:16:47.535984+00:00
-- url     : https://prove2.me/submissions/68a6f354-f892-486d-951f-8b954a81b1f4

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    ContDiffAt ℝ ∞ f u ∧ 0 < f u := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.2.2.1
