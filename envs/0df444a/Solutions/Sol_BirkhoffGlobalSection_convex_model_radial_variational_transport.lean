-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_radial_variational_transport
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:16:43.087986+00:00
-- url     : https://prove2.me/submissions/e37a2a07-e44c-44f2-8100-4da033fe70aa

import Theorems.Thm_BirkhoffGlobalSection_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (R X : Phase → Phase) (q v : ℝ → Phase)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hvS : ∀ t, q t 0 * v t 0 + q t 1 * v t 1 +
      q t 2 * v t 2 + q t 3 * v t 3 = 0)
    (hR : ∀ t, DifferentiableAt ℝ R (q t))
    (hX : ∀ t, DifferentiableAt ℝ X ((gauge M.body (q t))⁻¹ • q t))
    (hpush : ∀ z ∈ unitThreeSphere,
      fderiv ℝ (fun u : Phase => (gauge M.body u)⁻¹ • u) z (R z) =
        X ((gauge M.body z)⁻¹ • z))
    (hq : ∀ t, HasDerivAt q (R (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ R (q t) (v t)) t),
    let G : Phase → Phase := fun u => (gauge M.body u)⁻¹ • u
    (∀ t, HasDerivAt (fun s => G (q s)) (X (G (q t))) t) ∧
    (∀ t, HasDerivAt (fun s => fderiv ℝ G (q s) (v s))
      (fderiv ℝ X (G (q t)) (fderiv ℝ G (q t) (v t))) t) := by
  exact BirkhoffGlobalSection.radial_variation_bundle.2.2.2.2.2.1
