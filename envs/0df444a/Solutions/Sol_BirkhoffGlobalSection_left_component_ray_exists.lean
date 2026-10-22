-- Prove2me | solution 1 for BirkhoffGlobalSection.left_component_ray_exists
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T10:12:08.668595+00:00
-- url     : https://prove2.me/submissions/380e2dd5-a62c-4359-a4d0-20a0791876f7

import Theorems.Thm_BirkhoffGlobalSection_left_ray_positive_energy_before_second_collision
import Theorems.Thm_BirkhoffGlobalSection_left_first_radial_crossing_belongs_to_component

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧
      (fun i : Fin 4 => r * x i) ∈ leftEnergyComponent μ c := by
  intro x hx
  obtain ⟨R, hR, hpositive, hfree⟩ :=
    left_ray_positive_energy_before_second_collision μ c hμ0 hμ1 hc x hx
  exact left_first_radial_crossing_belongs_to_component μ c hμ0 hμ1 hc
    x hx R hR hpositive hfree
