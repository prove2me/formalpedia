-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_regularization_model_local_subcritical
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-01T01:06:48.893423+00:00
-- url     : https://prove2.me/submissions/150bdb09-575a-4d7e-b49d-c45463157d4a

import Theorems.Thm_BirkhoffGlobalSection_eh_left_regularization_local_subcritical
import Theorems.Thm_BirkhoffGlobalSection_eh_left_convex_body_local_subcritical

open BirkhoffGlobalSection

/-- Combine the EH coordinate identification with local convexity of the same
explicit EH component. The two analytic obligations remain separate children. -/
theorem solution
    (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        Nonempty (ConvexRegularizationModel μ c) := by
  obtain ⟨ε₁, η₁, hε₁, hη₁, htransport⟩ :=
    eh_left_regularization_local_subcritical c₀ hc₀
  obtain ⟨ε₂, η₂, hε₂, hη₂, hconvex⟩ :=
    eh_left_convex_body_local_subcritical c₀ hc₀
  refine ⟨min ε₁ ε₂, min η₁ η₂, lt_min hε₁ hε₂, lt_min hη₁ hη₂, ?_⟩
  intro μ c hμ0 hμ1 hμ hc hsub
  obtain ⟨M, hHamiltonian, hImage⟩ := htransport μ c hμ0 hμ1
    (lt_of_lt_of_le hμ (min_le_left _ _))
    (lt_of_lt_of_le hc (min_le_left _ _)) hsub
  obtain ⟨B, hcompact, hbody, horigin, hfrontier, hhessian⟩ :=
    hconvex μ c hμ0 hμ1
      (lt_of_lt_of_le hμ (min_le_right _ _))
      (lt_of_lt_of_le hc (min_le_right _ _)) hsub
  have hImageFrontier : M.toModel '' leftEnergyComponent μ c = frontier B :=
    hImage.trans hfrontier
  refine ⟨{
    source := M.source
    target := M.target
    source_open := M.source_open
    target_open := M.target_open
    contains_component := M.contains_component
    toModel := M.toModel
    fromModel := M.fromModel
    toModel_mapsTo := M.toModel_mapsTo
    fromModel_mapsTo := M.fromModel_mapsTo
    left_inverse := M.left_inverse
    right_inverse := M.right_inverse
    toModel_smooth := M.toModel_smooth
    fromModel_smooth := M.fromModel_smooth
    symplecticScale := M.symplecticScale
    symplecticScale_pos := M.symplecticScale_pos
    symplectic := M.symplectic
    antipodal := M.antipodal
    body := B
    body_compact := hcompact
    body_convex := hbody
    origin_interior := horigin
    image_frontier := hImageFrontier
    modelHamiltonian := M.modelHamiltonian
    model_smooth := M.model_smooth
    model_zero := ?_
    model_regular := ?_
    model_hessian := ?_
    timeScale := M.timeScale
    timeScale_continuous := M.timeScale_continuous
    timeScale_pos := M.timeScale_pos
    vectorField := M.vectorField }⟩
  · intro y hy
    obtain ⟨s, hs, rfl⟩ := hImageFrontier.symm ▸ hy
    exact M.model_zero s hs
  · intro y hy
    obtain ⟨s, hs, rfl⟩ := hImageFrontier.symm ▸ hy
    exact M.model_regular s hs
  · rw [hHamiltonian]
    exact hhessian
