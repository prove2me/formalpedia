-- Prove2me | solution 2 for BirkhoffGlobalSection.eh_left_convex_body
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T08:24:40.990022+00:00
-- url     : https://prove2.me/submissions/c70da50c-5e9e-414d-bbbc-5d178c44d8c3

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical
import Theorems.Thm_BirkhoffGlobalSection_convex_body_of_star_shaped_level_set
import Theorems.Thm_BirkhoffGlobalSection_eh_left_component_radial_graph
import Theorems.Thm_BirkhoffGlobalSection_eh_left_component_regular_compact_starshaped
import Theorems.Thm_BirkhoffGlobalSection_eh_left_tangential_hessian_positive

open BirkhoffGlobalSection

theorem solution
    (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧
          (0 : Phase) ∈ interior B ∧
          ehLeftEnergyComponent μ c = frontier B := by
  obtain ⟨ε₁, η₁, hε₁, hη₁, h₁⟩ := eh_left_component_regular_compact_starshaped c₀ hc₀
  obtain ⟨ε₂, η₂, hε₂, hη₂, h₂⟩ := eh_left_tangential_hessian_positive c₀ hc₀
  obtain ⟨ε₃, η₃, hε₃, hη₃, h₃⟩ := eh_left_component_radial_graph c₀ hc₀
  refine ⟨min ε₁ (min ε₂ ε₃), min η₁ (min η₂ η₃), by positivity, by positivity, ?_⟩
  intro μ c hμ0 hμ1 hμ hc hsub
  have hμ' : ∀ ε, min ε₁ (min ε₂ ε₃) ≤ ε → |μ - 1 / 2| < ε := fun ε hε => lt_of_lt_of_le hμ hε
  have hc' : ∀ η, min η₁ (min η₂ η₃) ≤ η → |c - c₀| < η := fun η hη => lt_of_lt_of_le hc hη
  obtain ⟨hcpt, hreg, -⟩ := h₁ μ c hμ0 hμ1 (hμ' _ (min_le_left _ _)) (hc' _ (min_le_left _ _)) hsub
  have hTH := h₂ μ c hμ0 hμ1
    (hμ' _ ((min_le_right _ _).trans (min_le_left _ _)))
    (hc' _ ((min_le_right _ _).trans (min_le_left _ _))) hsub
  obtain ⟨hray, huniq, hneg⟩ := h₃ μ c hμ0 hμ1
    (hμ' _ ((min_le_right _ _).trans (min_le_right _ _)))
    (hc' _ ((min_le_right _ _).trans (min_le_right _ _))) hsub
  have hF0 : ∀ s ∈ ehLeftEnergyComponent μ c, ehLeftHamiltonian μ c s = 0 := by
    intro s hs
    unfold ehLeftEnergyComponent at hs
    have h := connectedComponentIn_subset _ _ hs
    exact h
  exact convex_body_of_star_shaped_level_set (ehLeftHamiltonian μ c) (ehLeftEnergyComponent μ c)
    hcpt hF0 hreg hTH hray huniq hneg
