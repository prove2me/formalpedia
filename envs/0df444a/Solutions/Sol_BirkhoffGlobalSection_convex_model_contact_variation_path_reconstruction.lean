-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_variation_path_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:46.690384+00:00
-- url     : https://prove2.me/submissions/e673dad9-328a-41bb-b010-d9d2d11ce1ac

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
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
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (p : Plane),
    let e := p 0 • convexModelSymplecticContactFrame M (q 0) 0 +
      p 1 • convexModelSymplecticContactFrame M (q 0) 1
    ∀ t, (q t 0 * Z t e 0 + q t 1 * Z t e 1 +
        q t 2 * Z t e 2 + q t 3 * Z t e 3 = 0) ∧
      phaseRadialContact (q t) (Z t e) = 0 ∧
      Z t e = convexModelContactVariationPath M q Z t p 0 •
          convexModelSymplecticContactFrame M (q t) 0 +
        convexModelContactVariationPath M q Z t p 1 •
          convexModelSymplecticContactFrame M (q t) 1 := by
  exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.2.2.2.2.2.2.2.2
