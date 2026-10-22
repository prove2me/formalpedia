-- Prove2me | solution 1 for BirkhoffGlobalSection.sphere_reeb_extension_regular
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:16:46.399712+00:00
-- url     : https://prove2.me/submissions/0208ab92-82df-4e0d-a1d3-ac91140bbd38

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : ContDiffAt ℝ ∞ f u) (hp : 0 < f u),
    ContDiffAt ℝ ∞ (sphereReebExtension f) u ∧
    (u 0 * sphereReebExtension f u 0 + u 1 * sphereReebExtension f u 1 +
      u 2 * sphereReebExtension f u 2 + u 3 * sphereReebExtension f u 3 = 0) ∧
    f u * phaseRadialContact u (sphereReebExtension f u) = 1 ∧
    (∀ w : Phase, u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
      fderiv ℝ (fun x => f x * phaseRadialContact x w) u (sphereReebExtension f u) -
        fderiv ℝ (fun x => f x * phaseRadialContact x (sphereReebExtension f u)) u w = 0) := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.1
