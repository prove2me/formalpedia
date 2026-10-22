-- Prove2me | solution 1 for BirkhoffGlobalSection.sphere_reeb_extension_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:16:48.655873+00:00
-- url     : https://prove2.me/submissions/f37304dd-1251-4ee7-a97a-0b39594eebb4

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (f : Phase → ℝ) (x : Phase)
    (hx : 0 < zNormSq x + wNormSq x)
    (hf : ContDiffAt ℝ ∞ f (radialNormalize x)) (hp : 0 < f (radialNormalize x)),
    x 0 * sphereReebExtension f x 0 + x 1 * sphereReebExtension f x 1 +
      x 2 * sphereReebExtension f x 2 + x 3 * sphereReebExtension f x 3 = 0 := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.2.2.2.2.1
