-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_smooth_sphere_reeb_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:16:48.104782+00:00
-- url     : https://prove2.me/submissions/00b86a18-5e87-420f-a84f-bd6853173263

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
    let R : Phase → Phase := sphereReebExtension f
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    let y := G u
    ContDiffAt ℝ ∞ R u ∧
      fderiv ℝ G u (R u) =
        (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
          hamiltonianVectorField M.modelHamiltonian y := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.2.2.2.1
