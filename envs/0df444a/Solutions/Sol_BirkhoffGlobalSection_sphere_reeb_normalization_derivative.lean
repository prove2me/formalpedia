-- Prove2me | solution 1 for BirkhoffGlobalSection.sphere_reeb_normalization_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:41.702432+00:00
-- url     : https://prove2.me/submissions/59f601cb-ddf5-4264-81c7-4aab2fc7ad75

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (f : Phase → ℝ) (u w : Phase)
    (hu : u ∈ unitThreeSphere)
    (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0)
    (hf : ∀ x ∈ unitThreeSphere, ContDiffAt ℝ ∞ f x ∧ 0 < f x),
    let R := sphereReebExtension f
    fderiv ℝ f u w * phaseRadialContact u (R u) +
      f u * (phaseRadialContact w (R u) +
        phaseRadialContact u (fderiv ℝ R u w)) = 0 := by
  exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.1
