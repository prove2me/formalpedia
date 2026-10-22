-- Prove2me | solution 1 for BirkhoffGlobalSection.eh_left_convex_body_local_subcritical
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-01T18:03:04.028323+00:00
-- url     : https://prove2.me/submissions/1ec21134-bd1d-4cef-a1cc-55e5977584c2

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical
import Theorems.Thm_BirkhoffGlobalSection_eh_left_convex_body
import Theorems.Thm_BirkhoffGlobalSection_eh_left_tangential_hessian_positive

open BirkhoffGlobalSection

theorem solution
    (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧
          (0 : Phase) ∈ interior B ∧
          ehLeftEnergyComponent μ c = frontier B ∧
          HasPositiveTangentialHessianOn (ehLeftHamiltonian μ c) (frontier B) := by
  obtain ⟨ε₁, η₁, hε₁, hη₁, hbody⟩ := eh_left_convex_body c₀ hc₀
  obtain ⟨ε₂, η₂, hε₂, hη₂, hhess⟩ := eh_left_tangential_hessian_positive c₀ hc₀
  refine ⟨min ε₁ ε₂, min η₁ η₂, lt_min hε₁ hε₂, lt_min hη₁ hη₂, ?_⟩
  intro μ c hμ0 hμ1 hμ hcc hsub
  obtain ⟨B, hcompact, hconvex, horigin, hfront⟩ :=
    hbody μ c hμ0 hμ1 (lt_of_lt_of_le hμ (min_le_left _ _))
      (lt_of_lt_of_le hcc (min_le_left _ _)) hsub
  have hH := hhess μ c hμ0 hμ1 (lt_of_lt_of_le hμ (min_le_right _ _))
    (lt_of_lt_of_le hcc (min_le_right _ _)) hsub
  rw [hfront] at hH
  exact ⟨B, hcompact, hconvex, horigin, hfront, hH⟩
