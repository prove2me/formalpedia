-- Prove2me | solution 1 for BirkhoffGlobalSection.plane_family_winding_interval
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:07:36.311488+00:00
-- url     : https://prove2.me/submissions/c8f681e2-0c6b-4681-a618-08274e7cab6b

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
∀ (θ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (T : ℝ),
    ∃ a b : ℝ, a ≤ b ∧
      (fun s => (θ (T, s) - s) / (2 * Real.pi)) '' Icc 0 (2 * Real.pi) = Icc a b ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = a) ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = b) := by
  exact BirkhoffGlobalSection.contact_winding_interval_bundle.2.2.2.2.1
