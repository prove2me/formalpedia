-- Prove2me | solution 1 for BirkhoffGlobalSection.validated_range_retrograde_and_direct_global_sections
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T17:53:52.136334+00:00
-- url     : https://prove2.me/submissions/b170061f-9b93-4e49-a304-7d4715183163
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_convex_left_energy_component
import Theorems.Thm_BirkhoffGlobalSection_validated_binding_global_sections_of_convexity

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ γr γd : PeriodicOrbit φ,
      IsAstronomicallyRetrogradeOrbit φ γr ∧
      IsAstronomicallyDirectOrbit φ γd ∧
      DiskLikeGlobalSurfaceOfSection φ γr ∧
      DiskLikeGlobalSurfaceOfSection φ γd := by
  apply validated_binding_global_sections_of_convexity μ c hμ0 hμhalf hc0 hc1 φ hφ
  exact convex_left_energy_component μ c hμ0 hμhalf hc0 hc1
