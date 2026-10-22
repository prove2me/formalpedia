-- Prove2me | solution 1 for BirkhoffGlobalSection.winding_interval_width_of_pair_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:08:16.967908+00:00
-- url     : https://prove2.me/submissions/86345b64-abbc-456d-b46a-a8bafc5383cd

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_width_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (d : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (himage : d '' Icc 0 (2 * Real.pi) = Icc a b)
    (hbound : ∀ s r, |d r - d s| < 1 / 2),
    b - a < 1 / 2 := by
  exact BirkhoffGlobalSection.contact_winding_width_bundle.2.2.2.2.1
