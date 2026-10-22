-- Prove2me | solution 1 for BirkhoffGlobalSection.lower_winding_interval_integer_crossing
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:15:11.456457+00:00
-- url     : https://prove2.me/submissions/976e8485-21b0-4ded-978b-a391cdffea79

import Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (a b : ℝ) (k : ℤ)
    (ha : a < (k : ℝ)) (hb : (k : ℝ) < b) (hwidth : b - a < 1),
    Int.ceil a + Int.ceil b - 1 = 2 * k := by
  exact BirkhoffGlobalSection.winding_arithmetic_bundle.2.2.2.1
