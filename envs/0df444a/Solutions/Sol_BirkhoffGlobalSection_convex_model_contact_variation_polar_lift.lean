-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_variation_polar_lift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:07:32.246985+00:00
-- url     : https://prove2.me/submissions/1682923d-7b72-406d-9933-4153b6302f2c

import Theorems.Thm_BirkhoffGlobalSection_contact_angular_lift_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (p : Plane) (hp : p ≠ 0),
    ∃ ρ θ : ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧ (∀ t, 0 < ρ t) ∧
      ∀ t, convexModelContactVariationPath M q Z t p =
        ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)] := by
  exact BirkhoffGlobalSection.contact_angular_lift_bundle.2.2.2.2.2.1
