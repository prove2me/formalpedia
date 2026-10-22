-- Prove2me | solution 2 for BirkhoffGlobalSection.away_from_saddle_center_transverse_winding
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-29T23:40:44.762297+00:00
-- url     : https://prove2.me/submissions/36bc6205-2c06-4a23-9d98-92b746568778
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_regularization_model_convex_away_from_saddle_center
import Theorems.Thm_BirkhoffGlobalSection_dynamically_convex_on_strictly_convex_star_shaped_points
import Theorems.Thm_BirkhoffGlobalSection_regularization_model_pulls_back_dynamical_convexity

open BirkhoffGlobalSection

set_option autoImplicit false

theorem solution
    (U : Set Phase) (hU : IsOpen U)
    (hplus : (![1 / 2, 0, 0, 0] : Phase) ∈ U)
    (hminus : (![-(1 / 2), 0, 0, 0] : Phase) ∈ U) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
        ∀ (x : ℝ → Phase) (T : ℝ),
          IsPeriodicHamiltonianSolutionIn (leviCivitaHamiltonian μ c)
            (leftEnergyComponent μ c) x T →
          (∀ t : ℝ, x t ∉ U) →
          HasTransverseWindingAboveOne (leviCivitaHamiltonian μ c) x T := by
  obtain ⟨ε, η, hε, hη, hmodel⟩ :=
    regularization_model_convex_away_from_saddle_center U hU hplus hminus
  refine ⟨ε, η, hε, hη, ?_⟩
  intro μ c hμ0 hμ1 hμε hcη hc x T hx havoid
  obtain ⟨M, hM⟩ := hmodel μ c hμ0 hμ1 hμε hcη hc
  -- The model flow is dynamically convex on its strictly convex star-shaped
  -- points, and this pulls back to the Levi-Civita flow.
  have hpull := regularization_model_pulls_back_dynamical_convexity
    μ c hμ0 hμ1 hc M
    {y : Phase | IsStrictlyConvexStarShapedAt M.modelHamiltonian y}
    (dynamically_convex_on_strictly_convex_star_shaped_points M.modelHamiltonian)
  -- An orbit avoiding `U` stays where the model is strictly convex.
  obtain ⟨hT, hmem, hode, hclosed⟩ := hx
  exact hpull x T
    ⟨hT, fun t => ⟨hmem t, hM (x t) (hmem t) (havoid t)⟩, hode, hclosed⟩
