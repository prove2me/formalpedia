-- Prove2me | solution 1 for BirkhoffGlobalSection.sphere_reeb_variation_contact_conserved
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:42.359567+00:00
-- url     : https://prove2.me/submissions/10a44d4d-0628-414d-b9f0-63d5b1f5c2e0

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (f : Phase → ℝ) (q v : ℝ → Phase)
    (hf : ∀ u ∈ unitThreeSphere, ContDiffAt ℝ ∞ f u ∧ 0 < f u)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (sphereReebExtension f (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ (sphereReebExtension f) (q t) (v t)) t)
    (h0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0),
    ∀ t, f (q t) * phaseRadialContact (q t) (v t) =
      f (q 0) * phaseRadialContact (q 0) (v 0) := by
  exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.2.1
