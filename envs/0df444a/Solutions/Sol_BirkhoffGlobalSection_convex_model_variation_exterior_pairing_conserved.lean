-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_variation_exterior_pairing_conserved
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:51.191464+00:00
-- url     : https://prove2.me/submissions/945f1db2-0f49-408c-b00e-7327b6b68264

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q v w : ℝ → Phase)
    (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ (convexModelSphereReebField M) (q t) (v t)) t)
    (hw : ∀ t, HasDerivAt w (fderiv ℝ (convexModelSphereReebField M) (q t) (w t)) t)
    (hv0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0)
    (hw0 : q 0 0 * w 0 0 + q 0 1 * w 0 1 + q 0 2 * w 0 2 + q 0 3 * w 0 3 = 0),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    ∀ t, (fderiv ℝ (fun x => f x * phaseRadialContact x (w t)) (q t) (v t) -
      fderiv ℝ (fun x => f x * phaseRadialContact x (v t)) (q t) (w t)) =
      (fderiv ℝ (fun x => f x * phaseRadialContact x (w 0)) (q 0) (v 0) -
      fderiv ℝ (fun x => f x * phaseRadialContact x (v 0)) (q 0) (w 0)) := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.2.2.2.2.2.2.1
