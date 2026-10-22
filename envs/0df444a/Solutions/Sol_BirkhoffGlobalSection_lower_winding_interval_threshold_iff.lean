-- Prove2me | solution 1 for BirkhoffGlobalSection.lower_winding_interval_threshold_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:15:09.328984+00:00
-- url     : https://prove2.me/submissions/24be7e6f-2ce1-4531-b9e1-7f2d818ba300

import Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (a b : ℝ) (k : ℤ)
    (hab : a ≤ b) (hwidth : b - a < 1),
    2 * k + 1 ≤ Int.ceil a + Int.ceil b - 1 ↔ (k : ℝ) < a := by
  exact BirkhoffGlobalSection.winding_arithmetic_bundle.1
