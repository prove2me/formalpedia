-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_variation_path_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:07:27.310851+00:00
-- url     : https://prove2.me/submissions/71f00daa-b756-4dac-8c48-644b66c85a9d

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
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ),
    Function.Bijective (convexModelContactVariationPath M q Z t) := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.2.2.2.2.2.2.2.2.2.2.2.1
