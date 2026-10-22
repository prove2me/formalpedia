-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_frontier_tangent_curve
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:17:36.595926+00:00
-- url     : https://prove2.me/submissions/cd0dc119-45ff-4e66-aa2a-1a81e91bf15f

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y w : Phase) (hy : y ∈ frontier M.body)
    (hw : fderiv ℝ M.modelHamiltonian y w = 0),
    ∃ γ : ℝ → Phase, γ 0 = y ∧ HasDerivAt γ w 0 ∧
      ∀ᶠ s in 𝓝 0, γ s ∈ frontier M.body := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.2.2.2.1
