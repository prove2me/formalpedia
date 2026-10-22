-- Prove2me | solution 1 for BirkhoffGlobalSection.continuous_angle_gap_trapped
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:08:14.545314+00:00
-- url     : https://prove2.me/submissions/f879dfe4-0231-443a-b004-749668e351ca

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_width_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (g : ℝ → ℝ) (hg : Continuous g)
    (h0 : 0 < g 0) (hpi : g 0 < Real.pi)
    (hne0 : ∀ t, g t ≠ 0) (hnepi : ∀ t, g t ≠ Real.pi),
    ∀ t, 0 < g t ∧ g t < Real.pi := by
  exact BirkhoffGlobalSection.contact_winding_width_bundle.1
