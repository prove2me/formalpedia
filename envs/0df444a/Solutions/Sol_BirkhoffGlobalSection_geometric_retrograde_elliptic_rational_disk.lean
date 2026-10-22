-- Prove2me | solution 1 for BirkhoffGlobalSection.geometric_retrograde_elliptic_rational_disk
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-01T01:07:12.829571+00:00
-- url     : https://prove2.me/submissions/213fa0e9-a660-4249-a72a-42cde4fc36a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_geometric_retrograde_leviCivita_transverse_hopf
import Theorems.Thm_BirkhoffGlobalSection_convex_model_transports_transverse_hopf
import Theorems.Thm_BirkhoffGlobalSection_transverse_hopf_isotopy_spans_elliptic_disk

/-!
# The retrograde binding bounds a positive elliptic rational disk

1. In Levi-Civita coordinates, the normalized double lift of a geometric retrograde
   trajectory is equivariantly transversely isotopic to the positive standard Hopf
   circle (`geometric_retrograde_leviCivita_transverse_hopf`).
2. A convex regularization model carries this transverse Hopf class to the
   normalized model binding (`convex_model_transports_transverse_hopf`).
3. A set in the equivariant transverse Hopf class bounds a lifted rational disk
   with a single positive elliptic characteristic singularity
   (`transverse_hopf_isotopy_spans_elliptic_disk`).
-/

open BirkhoffGlobalSection
open scoped ContDiff

theorem solution
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (δ : AntipodalPeriodicTrajectory φ)
    (hδ : IsGeometricBirkhoffRetrogradeTrajectory φ δ) :
    Nonempty (PositiveEllipticRationalDisk
      (radialNormalize '' (M.toModel ''
        orbitSet (antipodalTrajectoryDoubleLift φ hanti δ)))) := by
  have hLC := geometric_retrograde_leviCivita_transverse_hopf μ c hμ0 hμ1 hc φ hφ hanti δ hδ
  obtain ⟨I⟩ := convex_model_transports_transverse_hopf μ c hμ0 hμ1 hc M φ hφ
    (antipodalTrajectoryDoubleLift φ hanti δ) hLC
  exact transverse_hopf_isotopy_spans_elliptic_disk _ I
