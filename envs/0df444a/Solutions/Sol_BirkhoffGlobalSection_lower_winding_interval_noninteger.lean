-- Prove2me | solution 1 for BirkhoffGlobalSection.lower_winding_interval_noninteger
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:15:10.696976+00:00
-- url     : https://prove2.me/submissions/5f94ba2c-cffa-4f82-8812-7ab6ec99ebc5

import Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (a b : ℝ) (k : ℤ)
    (ha : (k : ℝ) < a) (hab : a ≤ b) (hb : b < (k : ℝ) + 1),
    Int.ceil a + Int.ceil b - 1 = 2 * k + 1 := by
  exact BirkhoffGlobalSection.winding_arithmetic_bundle.2.2.1
