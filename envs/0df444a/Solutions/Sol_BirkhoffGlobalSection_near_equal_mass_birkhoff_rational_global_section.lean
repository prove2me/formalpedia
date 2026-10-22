-- Prove2me | solution 1 for BirkhoffGlobalSection.near_equal_mass_birkhoff_rational_global_section
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-26T18:21:55.551896+00:00
-- url     : https://prove2.me/submissions/3294326f-a3d5-49b8-be39-85fb0ee26234
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_birkhoff_retrograde_orbit_exists
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_geometry
import Theorems.Thm_BirkhoffGlobalSection_antipodal_trajectory_double_lift_is_double_cover
import Theorems.Thm_BirkhoffGlobalSection_near_equal_mass_lifted_retrograde_page
import Theorems.Thm_BirkhoffGlobalSection_lifted_rational_page_descends

open BirkhoffGlobalSection

set_option autoImplicit false

theorem solution :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ hanti : IsAntipodallyEquivariantFlow μ c φ,
          ∃ δ : AntipodalPeriodicTrajectory φ,
            IsGeometricBirkhoffRetrogradeTrajectory φ δ ∧
              RationalDiskLikeGlobalSurfaceOfSection φ hanti
                (antipodalTrajectoryDoubleLift φ hanti δ) := by
  obtain ⟨ε₀, hε₀, hpages⟩ := near_equal_mass_lifted_retrograde_page
  refine ⟨min ε₀ (1 / 2), lt_min hε₀ (by norm_num), min_le_right _ _, ?_⟩
  intro μ c hμ0 hμ1 hμ hc φ hφ hanti
  obtain ⟨δ, hδ⟩ := birkhoff_retrograde_orbit_exists μ c hμ0 hμ1 hc φ hφ
  have hgeometry := left_energy_component_geometry μ c hμ0 hμ1 hc
  have hinv := hgeometry.2.2.1
  have hfree := hgeometry.2.2.2.1
  obtain ⟨P⟩ := hpages μ c hμ0 hμ1 (lt_of_lt_of_le hμ (min_le_left _ _))
    hc φ hφ hanti δ hδ
  exact ⟨δ, hδ, lifted_rational_page_descends φ hanti hinv hfree
    (antipodalTrajectoryDoubleLift φ hanti δ)
    (antipodal_trajectory_double_lift_is_double_cover φ hanti hfree δ) P⟩
