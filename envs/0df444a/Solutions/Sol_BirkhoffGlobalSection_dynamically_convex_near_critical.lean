-- Prove2me | solution 1 for BirkhoffGlobalSection.dynamically_convex_near_critical
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-28T00:47:50.383387+00:00
-- url     : https://prove2.me/submissions/67fb0f22-49dd-4ea2-bdee-b3dac2db4916
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_saddle_center_neighborhood_transverse_winding
import Theorems.Thm_BirkhoffGlobalSection_away_from_saddle_center_transverse_winding

open BirkhoffGlobalSection

set_option autoImplicit false

theorem solution :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
        IsDynamicallyConvexOn (leviCivitaHamiltonian μ c)
          (leftEnergyComponent μ c) := by
  obtain ⟨U, hU, hplus, hminus, ε₁, η₁, hε₁, hη₁, hnear⟩ :=
    saddle_center_neighborhood_transverse_winding
  obtain ⟨ε₂, η₂, hε₂, hη₂, haway⟩ :=
    away_from_saddle_center_transverse_winding U hU hplus hminus
  refine ⟨min ε₁ ε₂, min η₁ η₂, lt_min hε₁ hε₂, lt_min hη₁ hη₂, ?_⟩
  intro μ c hμ0 hμ1 hμε hcη hc x T hx
  have hμ₁ : |μ - 1 / 2| < ε₁ := lt_of_lt_of_le hμε (min_le_left _ _)
  have hμ₂ : |μ - 1 / 2| < ε₂ := lt_of_lt_of_le hμε (min_le_right _ _)
  have hc₁ : c < 2 + η₁ :=
    lt_of_lt_of_le hcη (add_le_add_right (min_le_left _ _) _)
  have hc₂ : c < 2 + η₂ :=
    lt_of_lt_of_le hcη (add_le_add_right (min_le_right _ _) _)
  by_cases hmeet : ∃ t : ℝ, x t ∈ U
  · exact hnear μ c hμ0 hμ1 hμ₁ hc₁ hc x T hx hmeet
  · exact haway μ c hμ0 hμ1 hμ₂ hc₂ hc x T hx
      (fun t ht => hmeet ⟨t, ht⟩)
