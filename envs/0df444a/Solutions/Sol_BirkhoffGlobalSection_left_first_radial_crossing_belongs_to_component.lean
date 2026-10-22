-- Prove2me | solution 1 for BirkhoffGlobalSection.left_first_radial_crossing_belongs_to_component
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T10:23:10.486304+00:00
-- url     : https://prove2.me/submissions/ea2c8dda-1763-4549-ad27-91b82ea05a8c

import Theorems.Thm_BirkhoffGlobalSection_regularized_ray_first_zero_exists
import Theorems.Thm_BirkhoffGlobalSection_first_ray_zero_on_left_energy_component

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (x : Phase) (hx : x ∈ unitThreeSphere)
    (R : ℝ) (hR : 0 < R)
    (hpositive : 0 < leviCivitaHamiltonian μ c
      (fun i : Fin 4 => R * x i))
    (hfree : ∀ r : ℝ, 0 ≤ r → r ≤ R →
      0 < secondCollisionDistanceSq (fun i : Fin 4 => r * x i)) :
    ∃ r : ℝ, 0 < r ∧
      (fun i : Fin 4 => r * x i) ∈ leftEnergyComponent μ c := by
  obtain ⟨r, hr, hrR, hzero, hnegative⟩ :=
    regularized_ray_first_zero_exists μ c hμ0 hμ1 x R hR hpositive hfree
  refine ⟨r, hr, ?_⟩
  apply first_ray_zero_on_left_energy_component μ c hμ0 hμ1 hc
    x hx r hr hzero hnegative
  intro t ht htr
  exact hfree t ht (htr.trans hrR.le)
