-- Prove2me | solution 1 for BirkhoffGlobalSection.winding_image_strict_lower_bound_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:07:36.920223+00:00
-- url     : https://prove2.me/submissions/bf0c4d05-e32c-4720-bec5-248d8664f848

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
∀ (d : ℝ → ℝ) (a b c : ℝ)
    (hab : a ≤ b) (himage : d '' Icc 0 (2 * Real.pi) = Icc a b),
    (∀ s ∈ Icc 0 (2 * Real.pi), c < d s) ↔ c < a := by
  exact BirkhoffGlobalSection.contact_winding_interval_bundle.2.2.2.2.2.1
