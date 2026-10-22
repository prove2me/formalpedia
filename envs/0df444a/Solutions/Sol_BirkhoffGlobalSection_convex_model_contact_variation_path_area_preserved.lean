-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_variation_path_area_preserved
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:07:25.323634+00:00
-- url     : https://prove2.me/submissions/9d2de836-1d0d-43fc-bf4c-a1f10a0c8c5f

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
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
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ) (p r : Plane),
    convexModelContactVariationPath M q Z t p 0 * convexModelContactVariationPath M q Z t r 1 -
      convexModelContactVariationPath M q Z t p 1 * convexModelContactVariationPath M q Z t r 0 =
      p 0 * r 1 - p 1 * r 0 := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.2.2.2.2.2.2.2.2.1
