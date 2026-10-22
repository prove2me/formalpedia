-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_regularization_model_away_from_critical
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T15:02:24.301227+00:00
-- url     : https://prove2.me/submissions/ea0faa75-bff9-4084-a63f-109b2be9b3fa

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Theorems.Thm_BirkhoffGlobalSection_eh_left_regularization_subcritical
import Theorems.Thm_BirkhoffGlobalSection_eh_left_convex_body_away_from_critical

open BirkhoffGlobalSection

/-- The EH regularization model at every subcritical parameter, combined with the
uniform convex body of the same explicit component. -/
theorem solution (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → 2 + η ≤ c → belowFirstCriticalValue μ c →
        Nonempty (ConvexRegularizationModel μ c) := by
  obtain ⟨ε, hε, hconvex⟩ := eh_left_convex_body_away_from_critical η hη
  refine ⟨ε, hε, ?_⟩
  intro μ c hμ0 hμ1 hμ hc hsub
  obtain ⟨M, hHamiltonian, hImage⟩ := eh_left_regularization_subcritical μ c hμ0 hμ1 hsub
  obtain ⟨B, hcompact, hbody, horigin, hfrontier, hhessian⟩ :=
    hconvex μ c hμ0 hμ1 hμ hc hsub
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
