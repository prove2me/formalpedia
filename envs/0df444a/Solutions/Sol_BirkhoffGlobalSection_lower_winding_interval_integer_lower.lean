-- Prove2me | solution 1 for BirkhoffGlobalSection.lower_winding_interval_integer_lower
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:15:12.213143+00:00
-- url     : https://prove2.me/submissions/1c741770-0faf-40b4-95d9-e90a52c2c140

import Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (b : ℝ) (k : ℤ)
    (hb : (k : ℝ) < b) (hwidth : b - (k : ℝ) < 1),
    Int.ceil (k : ℝ) + Int.ceil b - 1 = 2 * k := by
  exact BirkhoffGlobalSection.winding_arithmetic_bundle.2.2.2.2.2.1
