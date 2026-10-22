-- Prove2me | solution 1 for BirkhoffGlobalSection.quotient_retrograde_page_near_critical
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T14:27:28.659916+00:00
-- url     : https://prove2.me/submissions/ebc49ae3-de6d-46c8-b701-32f40e5a2a46
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_lifted_retrograde_page_near_critical
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_geometry
import Theorems.Thm_BirkhoffGlobalSection_antipodal_trajectory_double_lift_is_double_cover
import Theorems.Thm_BirkhoffGlobalSection_lifted_rational_page_descends

open BirkhoffGlobalSection

set_option autoImplicit false

theorem solution :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ (hanti : IsAntipodallyEquivariantFlow μ c φ)
            (δ : AntipodalPeriodicTrajectory φ),
            IsGeometricBirkhoffRetrogradeTrajectory φ δ →
            RationalDiskLikeGlobalSurfaceOfSection φ hanti
              (antipodalTrajectoryDoubleLift φ hanti δ) := by
  obtain ⟨ε, η, hε, hη, hpages⟩ := lifted_retrograde_page_near_critical
  refine ⟨ε, η, hε, hη, ?_⟩
  intro μ c hμ0 hμ1 hμε hηc hc φ hφ hanti δ hδ
  have hgeometry := left_energy_component_geometry μ c hμ0 hμ1 hc
  have hinv := hgeometry.2.2.1
  have hfree := hgeometry.2.2.2.1
  obtain ⟨P⟩ := hpages μ c hμ0 hμ1 hμε hηc hc φ hφ hanti δ hδ
  exact lifted_rational_page_descends φ hanti hinv hfree
    (antipodalTrajectoryDoubleLift φ hanti δ)
    (antipodal_trajectory_double_lift_is_double_cover φ hanti hfree δ) P
