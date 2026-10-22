-- Prove2me | solution 1 for BirkhoffGlobalSection.first_ray_zero_on_left_energy_component
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T12:27:17.773648+00:00
-- url     : https://prove2.me/submissions/88a36f8a-08ad-49ee-96ee-561b60bc2e3a

import Theorems.Thm_BirkhoffGlobalSection_first_ray_zero_in_left_negative_closure
import Theorems.Thm_BirkhoffGlobalSection_left_negative_boundary_zero_in_energy_component

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (x : Phase) (hx : x ∈ unitThreeSphere)
    (r : ℝ) (hr : 0 < r)
    (hzero : leviCivitaHamiltonian μ c
      (fun i : Fin 4 => r * x i) = 0)
    (hnegative : ∀ t : ℝ, 0 ≤ t → t < r →
      leviCivitaHamiltonian μ c (fun i : Fin 4 => t * x i) < 0)
    (hfree : ∀ t : ℝ, 0 ≤ t → t ≤ r →
      0 < secondCollisionDistanceSq (fun i : Fin 4 => t * x i)) :
    (fun i : Fin 4 => r * x i) ∈ leftEnergyComponent μ c := by
  have hclosure :=
    first_ray_zero_in_left_negative_closure μ c hμ0 hμ1 x r hr hnegative hfree
  exact left_negative_boundary_zero_in_energy_component μ c hμ0 hμ1 hc
    (fun i : Fin 4 => r * x i) hclosure hzero
    (hfree r (le_of_lt hr) (le_refl r))
