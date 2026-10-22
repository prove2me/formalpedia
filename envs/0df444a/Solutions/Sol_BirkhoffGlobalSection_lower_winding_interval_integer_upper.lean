-- Prove2me | solution 1 for BirkhoffGlobalSection.lower_winding_interval_integer_upper
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:15:52.855993+00:00
-- url     : https://prove2.me/submissions/f8b49270-15c3-4621-989b-20245766b3f3

import Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (a : ℝ) (k : ℤ)
    (ha : a ≤ (k : ℝ)) (hwidth : (k : ℝ) - a < 1),
    Int.ceil a + Int.ceil (k : ℝ) - 1 = 2 * k - 1 := by
  exact BirkhoffGlobalSection.winding_arithmetic_bundle.2.2.2.2.1
