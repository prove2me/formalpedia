-- Prove2me | solution 1 for BirkhoffGlobalSection.lifted_retrograde_page_local_subcritical
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T01:36:06.233325+00:00
-- url     : https://prove2.me/submissions/2e94d718-0c98-49bb-8c4c-2f1d21e765be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_convex_regularization_model_local_subcritical
import Theorems.Thm_BirkhoffGlobalSection_geometric_retrograde_page_of_convex_regularization
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_geometry
import Mathlib.Topology.Order.Compact

open BirkhoffGlobalSection

set_option autoImplicit false

/-- A continuous positive regularized clock has uniform positive lower and
finite upper bounds on the compact energy component. -/
private theorem clock_bounds {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    (hcompact : IsCompact (leftEnergyComponent μ c))
    (hne : (leftEnergyComponent μ c).Nonempty) :
    ∃ a b : ℝ, 0 < a ∧ ∀ s ∈ leftEnergyComponent μ c,
      a ≤ M.timeScale s ∧ M.timeScale s ≤ b := by
  have hcontinuous : ContinuousOn M.timeScale (leftEnergyComponent μ c) :=
    M.timeScale_continuous.mono M.contains_component
  obtain ⟨smin, hsmin, hmin⟩ := hcompact.exists_isMinOn hne hcontinuous
  obtain ⟨smax, hsmax, hmax⟩ := hcompact.exists_isMaxOn hne hcontinuous
  refine ⟨M.timeScale smin, M.timeScale smax, M.timeScale_pos smin hsmin, ?_⟩
  intro s hs
  exact ⟨hmin hs, hmax hs⟩

theorem solution
    (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ (hanti : IsAntipodallyEquivariantFlow μ c φ)
            (δ : AntipodalPeriodicTrajectory φ),
            IsGeometricBirkhoffRetrogradeTrajectory φ δ →
            Nonempty (LiftedRationalPage φ
              (antipodalTrajectoryDoubleLift φ hanti δ)) := by
  obtain ⟨ε, η, hε, hη, hmodels⟩ :=
    convex_regularization_model_local_subcritical c₀ hc₀
  refine ⟨ε, η, hε, hη, ?_⟩
  intro μ c hμ0 hμ1 hμε hcη hc φ hφ hanti δ hδ
  obtain ⟨M⟩ := hmodels μ c hμ0 hμ1 hμε hcη hc
  have hcompact := (left_energy_component_geometry μ c hμ0 hμ1 hc).1
  obtain ⟨a, b, ha, hclock⟩ := clock_bounds M hcompact ⟨δ.point, δ.point.property⟩
  exact geometric_retrograde_page_of_convex_regularization
    μ c hμ0 hμ1 hc M a b ha hclock φ hφ hanti δ hδ
