-- Prove2me | solution 1 for BirkhoffGlobalSection.geometric_retrograde_page_of_convex_regularization
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T01:54:39.753933+00:00
-- url     : https://prove2.me/submissions/acb2b55c-4439-4e6a-a38a-7780058d840b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_convex_regularization_model_dynamics
import Theorems.Thm_BirkhoffGlobalSection_convex_model_geometric_retrograde_page
import Theorems.Thm_BirkhoffGlobalSection_model_rational_page_pulls_back
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_geometry

open BirkhoffGlobalSection

set_option autoImplicit false

theorem solution
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (M : ConvexRegularizationModel μ c)
    (a b : ℝ) (ha : 0 < a)
    (hclock : ∀ s ∈ leftEnergyComponent μ c,
      a ≤ M.timeScale s ∧ M.timeScale s ≤ b)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (δ : AntipodalPeriodicTrajectory φ)
    (hδ : IsGeometricBirkhoffRetrogradeTrajectory φ δ) :
    Nonempty (LiftedRationalPage φ
      (antipodalTrajectoryDoubleLift φ hanti δ)) := by
  obtain ⟨D⟩ := convex_regularization_model_dynamics
    μ c hμ0 hμ1 hc M a b ha hclock φ hφ
  obtain ⟨P⟩ := convex_model_geometric_retrograde_page
    μ c hμ0 hμ1 hc M φ hφ hanti δ hδ D
  have hinv := (left_energy_component_geometry μ c hμ0 hμ1 hc).2.2.1
  exact model_rational_page_pulls_back M hinv φ D
    (antipodalTrajectoryDoubleLift φ hanti δ) P
