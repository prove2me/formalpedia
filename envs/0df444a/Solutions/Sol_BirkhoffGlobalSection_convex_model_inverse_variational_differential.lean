-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_inverse_variational_differential
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:17:39.315836+00:00
-- url     : https://prove2.me/submissions/7d64f129-596a-4c6a-ae0e-c269248ff2d0

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y w : Phase) (hy : y ∈ frontier M.body)
    (hw : fderiv ℝ M.modelHamiltonian y w = 0),
    let X : Phase → Phase := fun z =>
      (phaseRadialContact z (hamiltonianVectorField M.modelHamiltonian z))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian z
    fderiv ℝ (fderiv ℝ radialNormalize) y (X y) w +
      fderiv ℝ radialNormalize y (fderiv ℝ X y w) =
      fderiv ℝ (convexModelSphereReebField M) (radialNormalize y)
        (fderiv ℝ radialNormalize y w) := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.2.2.2.2.2.2.2.1
