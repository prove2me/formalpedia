-- Prove2me | solution 1 for BirkhoffGlobalSection.plane_linear_area_preserving_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:07:26.537476+00:00
-- url     : https://prove2.me/submissions/5c7ac5a6-7d48-47a0-a745-f7229310d526

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (A : Plane → Plane)
    (hlin : ∀ (p r : Plane) (a b : ℝ), A (a • p + b • r) = a • A p + b • A r)
    (harea : ∀ p r, A p 0 * A r 1 - A p 1 * A r 0 = p 0 * r 1 - p 1 * r 0),
    Function.Bijective A := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.2.2.2.2.2.2.2.2.2.2.1
