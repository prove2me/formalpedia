-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_gauge_chart_mem_frontier
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:17:35.806804+00:00
-- url     : https://prove2.me/submissions/c6a7d0e3-3552-4e04-995e-8f6b7d1461bc

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ≠ 0),
    (gauge M.body u)⁻¹ • u ∈ frontier M.body := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.2.2.1
