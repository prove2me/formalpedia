-- Prove2me | solution 1 for BirkhoffGlobalSection.lower_winding_interval_left_stable
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:15:53.557978+00:00
-- url     : https://prove2.me/submissions/0995aa37-969c-43b9-84ad-d32add8bc8e0

import Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (a b : ℝ),
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      Int.ceil (a - ε) + Int.ceil (b - ε) - 1 = Int.ceil a + Int.ceil b - 1 := by
  exact BirkhoffGlobalSection.winding_arithmetic_bundle.2.2.2.2.2.2
