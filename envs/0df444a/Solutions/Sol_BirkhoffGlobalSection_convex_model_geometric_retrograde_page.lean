-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_geometric_retrograde_page
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T02:12:26.489581+00:00
-- url     : https://prove2.me/submissions/aa82b75d-bf67-4af0-820d-1c09af71328a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_geometric_retrograde_transverse_hopf
import Theorems.Thm_BirkhoffGlobalSection_convex_model_page_of_transverse_hopf
import Theorems.Thm_BirkhoffGlobalSection_convex_model_periodic_orbit_transport
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_geometry
import Theorems.Thm_BirkhoffGlobalSection_antipodal_trajectory_double_lift_is_double_cover

open BirkhoffGlobalSection

set_option autoImplicit false

theorem solution
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (δ : AntipodalPeriodicTrajectory φ)
    (hδ : IsGeometricBirkhoffRetrogradeTrajectory φ δ)
    (D : ConvexModelDynamics M φ) :
    Nonempty (ConvexModelRationalPage M D
      (antipodalTrajectoryDoubleLift φ hanti δ)) := by
  obtain ⟨_, _, hinv, hfree, _⟩ := left_energy_component_geometry μ c hμ0 hμ1 hc
  let γ := antipodalTrajectoryDoubleLift φ hanti δ
  have hsimple : IsSimplePeriodicOrbit φ γ :=
    (antipodal_trajectory_double_lift_is_double_cover φ hanti hfree δ).1
  obtain ⟨hmodel_simple, htrace⟩ :=
    convex_model_periodic_orbit_transport M φ D γ hsimple
  have hsymmetric : ∀ y ∈ frontier M.body, -y ∈ frontier M.body := by
    intro y hy
    rw [← M.image_frontier] at hy ⊢
    obtain ⟨s, hs, rfl⟩ := hy
    refine ⟨-s, (hinv s).mp hs, ?_⟩
    exact M.antipodal s hs
  have hHopf := geometric_retrograde_transverse_hopf μ c hμ0 hμ1 hc M φ hφ hanti δ hδ
  apply convex_model_page_of_transverse_hopf M φ D γ
    (D.mapPeriodicOrbit γ) hmodel_simple htrace hsymmetric
  rw [htrace]
  exact hHopf
