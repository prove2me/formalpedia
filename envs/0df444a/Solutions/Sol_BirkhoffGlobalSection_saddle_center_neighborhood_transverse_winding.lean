-- Prove2me | solution 1 for BirkhoffGlobalSection.saddle_center_neighborhood_transverse_winding
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-28T02:38:11.409166+00:00
-- url     : https://prove2.me/submissions/deb72951-1c4f-40b9-9fa9-c6a3bece6a04

import Theorems.Thm_BirkhoffGlobalSection_saddle_center_long_residence_transverse_winding
import Theorems.Thm_BirkhoffGlobalSection_saddle_center_arbitrarily_long_residence

open BirkhoffGlobalSection

theorem solution :
    ∃ U : Set Phase, IsOpen U ∧
      (![1 / 2, 0, 0, 0] : Phase) ∈ U ∧ (![-(1 / 2), 0, 0, 0] : Phase) ∈ U ∧
      ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
        ∀ μ c : ℝ, 0 < μ → μ < 1 →
          |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
          ∀ (x : ℝ → Phase) (T : ℝ),
            IsPeriodicHamiltonianSolutionIn (leviCivitaHamiltonian μ c)
              (leftEnergyComponent μ c) x T →
            (∃ t : ℝ, x t ∈ U) →
            HasTransverseWindingAboveOne (leviCivitaHamiltonian μ c) x T := by
  obtain ⟨U, hU, hp, hm, ε₁, η₁, L, hε₁, hη₁, hL, hindex⟩ :=
    saddle_center_long_residence_transverse_winding
  obtain ⟨V, hV, _, hvp, hvm, ε₂, η₂, hε₂, hη₂, hresidence⟩ :=
    saddle_center_arbitrarily_long_residence U hU hp hm L hL
  refine ⟨V, hV, hvp, hvm, min ε₁ ε₂, min η₁ η₂,
    lt_min hε₁ hε₂, lt_min hη₁ hη₂, ?_⟩
  intro μ c hμ0 hμ1 hμ hc hsub x T hx hvisit
  have hμ₁ : |μ - 1 / 2| < ε₁ := lt_of_lt_of_le hμ (min_le_left _ _)
  have hμ₂ : |μ - 1 / 2| < ε₂ := lt_of_lt_of_le hμ (min_le_right _ _)
  have hc₁ : c < 2 + η₁ :=
    lt_of_lt_of_le hc (add_le_add (le_refl (2 : ℝ)) (min_le_left _ _))
  have hc₂ : c < 2 + η₂ :=
    lt_of_lt_of_le hc (add_le_add (le_refl (2 : ℝ)) (min_le_right _ _))
  obtain ⟨hLT, hsegment⟩ := hresidence μ c hμ0 hμ1 hμ₂ hc₂ hsub x T hx hvisit
  exact hindex μ c hμ0 hμ1 hμ₁ hc₁ hsub x T hx hLT hsegment
