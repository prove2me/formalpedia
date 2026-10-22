-- Prove2me | solution 1 for BirkhoffGlobalSection.near_equal_mass_lifted_retrograde_page
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-26T20:44:52.971719+00:00
-- url     : https://prove2.me/submissions/287ccad2-d481-4f5c-8142-f4a7cc9b53bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_near_equal_mass_quotient_retrograde_page
import Theorems.Thm_BirkhoffGlobalSection_quotient_page_lifts_to_cover
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_geometry
import Theorems.Thm_BirkhoffGlobalSection_antipodal_trajectory_double_lift_is_double_cover
import Theorems.Thm_BirkhoffGlobalSection_antipodal_quotient_dynamics_continuous

open BirkhoffGlobalSection

set_option autoImplicit false

theorem solution :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε₀ → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ (hanti : IsAntipodallyEquivariantFlow μ c φ)
            (δ : AntipodalPeriodicTrajectory φ),
            IsGeometricBirkhoffRetrogradeTrajectory φ δ →
            Nonempty (LiftedRationalPage φ
              (antipodalTrajectoryDoubleLift φ hanti δ)) := by
  obtain ⟨ε₀, hε₀, hQ⟩ := near_equal_mass_quotient_retrograde_page
  refine ⟨ε₀, hε₀, ?_⟩
  intro μ c hμ0 hμ1 hμ hc φ hφ hanti δ hδ
  have hRat := hQ μ c hμ0 hμ1 hμ hc φ hφ hanti δ hδ
  obtain ⟨-, -, hinv, hfree, -⟩ :=
    left_energy_component_geometry μ c hμ0 hμ1 hc
  have hdouble :=
    antipodal_trajectory_double_lift_is_double_cover φ hanti hfree δ
  have hcont :=
    antipodal_quotient_dynamics_continuous φ hanti hinv hfree
  exact quotient_page_lifts_to_cover φ hanti hinv hfree hcont
    (antipodalTrajectoryDoubleLift φ hanti δ) hdouble hRat
