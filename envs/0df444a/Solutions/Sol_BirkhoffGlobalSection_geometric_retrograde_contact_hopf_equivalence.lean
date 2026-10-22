-- Prove2me | solution 1 for BirkhoffGlobalSection.geometric_retrograde_contact_hopf_equivalence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T04:59:18.21909+00:00
-- url     : https://prove2.me/submissions/83c05d40-a519-442f-976d-1e940d12b75b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_standard_hopf_elliptic_rational_disk
import Theorems.Thm_BirkhoffGlobalSection_geometric_retrograde_elliptic_rational_disk
import Theorems.Thm_BirkhoffGlobalSection_positive_elliptic_rational_disks_contact_equivalent

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
    ∃ F : EquivariantSphereContactomorphism,
      F.toFun '' (standardHopfCircle '' unitCircle) =
        radialNormalize '' (M.toModel ''
          orbitSet (antipodalTrajectoryDoubleLift φ hanti δ))  := by
  obtain ⟨D₀⟩ := standard_hopf_elliptic_rational_disk
  obtain ⟨D⟩ := geometric_retrograde_elliptic_rational_disk
    μ c hμ0 hμ1 hc M φ hφ hanti δ hδ
  exact positive_elliptic_rational_disks_contact_equivalent _ _ D₀ D

