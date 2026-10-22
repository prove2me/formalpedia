-- Prove2me | solution 1 for BirkhoffGlobalSection.winding_image_lower_rule_threshold_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:08:13.931444+00:00
-- url     : https://prove2.me/submissions/cb350910-182a-406c-bba1-eb0ee2b0c6ed

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_interval_bundle

open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology

set_option maxHeartbeats 800000
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (d : ℝ → ℝ) (a b : ℝ) (k : ℤ)
    (hab : a ≤ b) (hwidth : b - a < 1)
    (himage : d '' Icc 0 (2 * Real.pi) = Icc a b),
    2 * k + 1 ≤ Int.ceil a + Int.ceil b - 1 ↔
      ∀ s ∈ Icc 0 (2 * Real.pi), (k : ℝ) < d s := by
  exact BirkhoffGlobalSection.contact_winding_interval_bundle.2.2.2.2.2.2.2.2.2
