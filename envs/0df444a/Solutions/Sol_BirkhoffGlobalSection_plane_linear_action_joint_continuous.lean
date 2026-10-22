-- Prove2me | solution 1 for BirkhoffGlobalSection.plane_linear_action_joint_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:07:37.459994+00:00
-- url     : https://prove2.me/submissions/354f158f-d85d-4a01-a6b9-487fcc9b506c

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
∀ (A : ℝ → Plane → Plane)
    (hlin : ∀ t (p r : Plane) (a b : ℝ), A t (a • p + b • r) = a • A t p + b • A t r)
    (hcont : ∀ p, Continuous (fun t => A t p)),
    Continuous (fun x : ℝ × Plane => A x.1 x.2) := by
  exact BirkhoffGlobalSection.contact_winding_interval_bundle.2.2.2.2.2.2.1
