-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_complete_concrete_sphere_reeb_trajectories
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:17:32.453481+00:00
-- url     : https://prove2.me/submissions/d776e0e0-0cad-4cc6-8eb0-90c69763832d

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    {φ : Flow ℝ (LeftEnergyState μ c)} (D : ConvexModelDynamics M φ),
    ∃ θ : Flow ℝ {u : Phase // u ∈ unitThreeSphere},
      ∀ u t, HasDerivAt (fun s => (θ s u : Phase))
        (convexModelSphereReebField M (θ t u)) t := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.2.2.2.2.2.2.2.2.2
