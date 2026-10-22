-- Prove2me | solution 1 for BirkhoffGlobalSection.plane_area_preserving_injective
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:07:25.967029+00:00
-- url     : https://prove2.me/submissions/3b0de263-a7cb-4944-8f40-28f0c1839835

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (A : Plane → Plane)
    (hA : ∀ p r, A p 0 * A r 1 - A p 1 * A r 0 = p 0 * r 1 - p 1 * r 0),
    Function.Injective A := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.2.2.2.2.2.2.2.2.2.1
