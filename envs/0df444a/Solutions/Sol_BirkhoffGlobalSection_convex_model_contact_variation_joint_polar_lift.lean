-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_variation_joint_polar_lift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:08:12.459068+00:00
-- url     : https://prove2.me/submissions/02c0d282-6db4-47f4-a36d-8ac87809f969

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_interval_bundle

open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology

set_option maxHeartbeats 800000
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
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase),
    ∃ ρ θ : ℝ × ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧
      (∀ x, 0 < ρ x) ∧ (∀ s, θ (0, s) = s) ∧
      ∀ x, convexModelContactVariationPath M q Z x.1 ![Real.cos x.2, Real.sin x.2] =
        ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)] := by
  exact BirkhoffGlobalSection.contact_winding_interval_bundle.2.2.2.2.2.2.2.1
