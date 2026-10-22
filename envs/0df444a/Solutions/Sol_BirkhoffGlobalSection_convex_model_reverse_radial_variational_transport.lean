-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_reverse_radial_variational_transport
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:18:26.413005+00:00
-- url     : https://prove2.me/submissions/ba0bc89e-dae7-4660-9e21-a03c857cb39d

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (x v : ℝ → Phase)
    (hs : ∀ t, x t ∈ frontier M.body)
    (hx : ∀ t, HasDerivAt x
      ((phaseRadialContact (x t) (hamiltonianVectorField M.modelHamiltonian (x t)))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian (x t)) t)
    (hv : ∀ t, HasDerivAt v
      (fderiv ℝ (fun y =>
        (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
          hamiltonianVectorField M.modelHamiltonian y) (x t) (v t)) t)
    (h0 : fderiv ℝ M.modelHamiltonian (x 0) (v 0) = 0),
    let q : ℝ → Phase := fun t => radialNormalize (x t)
    let w : ℝ → Phase := fun t => fderiv ℝ radialNormalize (x t) (v t)
    (∀ t, q t ∈ unitThreeSphere) ∧
    (∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t) ∧
    (∀ t, HasDerivAt w (fderiv ℝ (convexModelSphereReebField M) (q t) (w t)) t) ∧
    (∀ t, q t 0 * w t 0 + q t 1 * w t 1 + q t 2 * w t 2 + q t 3 * w t 3 = 0) ∧
    (∀ t, fderiv ℝ (fun u : Phase => (gauge M.body u)⁻¹ • u) (q t) (w t) = v t) := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.2.2.2.2.2.2.2.2.2.2
