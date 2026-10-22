-- Prove2me | solution 1 for BirkhoffGlobalSection.lower_winding_interval_ge_three_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:15:09.946708+00:00
-- url     : https://prove2.me/submissions/f3317583-6674-4fde-b092-f939ffa7490e

import Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (a b : ℝ)
    (hab : a ≤ b) (hwidth : b - a < 1),
    (3 : ℤ) ≤ Int.ceil a + Int.ceil b - 1 ↔ 1 < a := by
  exact BirkhoffGlobalSection.winding_arithmetic_bundle.2.1
