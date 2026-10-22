-- Prove2me | solution 1 for BirkhoffGlobalSection.geometric_retrograde_transverse_hopf
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T04:40:21.716838+00:00
-- url     : https://prove2.me/submissions/609ea30c-b680-4895-a2f3-5ce8d1f3112d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_geometric_retrograde_contact_hopf_equivalence
import Theorems.Thm_BirkhoffGlobalSection_equivariant_sphere_contact_group_connected
import Theorems.Thm_BirkhoffGlobalSection_contact_isotopy_maps_hopf

open BirkhoffGlobalSection

theorem solution
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (δ : AntipodalPeriodicTrajectory φ)
    (hδ : IsGeometricBirkhoffRetrogradeTrajectory φ δ) :
    Nonempty (EquivariantTransverseHopfIsotopy
      (radialNormalize '' (M.toModel ''
        orbitSet (antipodalTrajectoryDoubleLift φ hanti δ))))  := by
  obtain ⟨F, hF⟩ := geometric_retrograde_contact_hopf_equivalence
    μ c hμ0 hμ1 hc M φ hφ hanti δ hδ
  obtain ⟨I⟩ := equivariant_sphere_contact_group_connected F
  simpa only [hF] using contact_isotopy_maps_hopf F I

