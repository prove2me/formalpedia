-- Prove2me | solution 1 for BirkhoffGlobalSection.quotient_retrograde_page_local_subcritical
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T01:18:50.2454+00:00
-- url     : https://prove2.me/submissions/c9e23e66-c017-43cc-a9c4-11108827620f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_lifted_retrograde_page_local_subcritical
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_geometry
import Theorems.Thm_BirkhoffGlobalSection_antipodal_trajectory_double_lift_is_double_cover
import Theorems.Thm_BirkhoffGlobalSection_lifted_rational_page_descends

open BirkhoffGlobalSection

set_option autoImplicit false

theorem solution (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ (hanti : IsAntipodallyEquivariantFlow μ c φ)
            (δ : AntipodalPeriodicTrajectory φ),
            IsGeometricBirkhoffRetrogradeTrajectory φ δ →
            RationalDiskLikeGlobalSurfaceOfSection φ hanti
              (antipodalTrajectoryDoubleLift φ hanti δ) := by
  obtain ⟨ε, η, hε, hη, hpages⟩ := lifted_retrograde_page_local_subcritical c₀ hc₀
  refine ⟨ε, η, hε, hη, ?_⟩
  intro μ c hμ0 hμ1 hμε hμη hc φ hφ hanti δ hδ
  have hgeometry := left_energy_component_geometry μ c hμ0 hμ1 hc
  have hinv := hgeometry.2.2.1
  have hfree := hgeometry.2.2.2.1
  obtain ⟨P⟩ := hpages μ c hμ0 hμ1 hμε hμη hc φ hφ hanti δ hδ
  exact lifted_rational_page_descends φ hanti hinv hfree
    (antipodalTrajectoryDoubleLift φ hanti δ)
    (antipodal_trajectory_double_lift_is_double_cover φ hanti hfree δ) P
