-- Prove2me | solution 1 for BirkhoffGlobalSection.polar_action_winding_pair_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:08:16.392051+00:00
-- url     : https://prove2.me/submissions/670fd69d-7a7c-4a47-9d12-1f92f2ce6d3c

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_width_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (θ : ℝ × ℝ → ℝ)
    (hshift : ∀ t s, θ (t, s + Real.pi) = θ (t, s) + Real.pi)
    (hgap : ∀ s r, s < r → r - s < Real.pi →
      ∀ t, 0 < θ (t, r) - θ (t, s) ∧ θ (t, r) - θ (t, s) < Real.pi)
    (T s r : ℝ),
    |((θ (T, r) - r) / (2 * Real.pi)) - ((θ (T, s) - s) / (2 * Real.pi))| < 1 / 2 := by
  exact BirkhoffGlobalSection.contact_winding_width_bundle.2.2.2.1
