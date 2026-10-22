-- Prove2me | solution 1 for BirkhoffGlobalSection.left_component_momentum_coordinates_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T08:08:46.228533+00:00
-- url     : https://prove2.me/submissions/f238406d-a6ae-478a-bde1-ede66eb6fde7

import Theorems.Thm_BirkhoffGlobalSection_left_component_position_coordinates_bounded
import Theorems.Thm_BirkhoffGlobalSection_left_component_second_collision_separated
import Theorems.Thm_BirkhoffGlobalSection_regular_energy_momentum_bound_from_coordinate_bounds

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ Rw : ℝ, ∀ s ∈ leftEnergyComponent μ c,
      |s 2| ≤ Rw ∧ |s 3| ≤ Rw := by
  obtain ⟨Rz, hRz⟩ :=
    left_component_position_coordinates_bounded μ c hμ0 hμ1 hc
  obtain ⟨δ, hδ, hsep⟩ :=
    left_component_second_collision_separated μ c hμ0 hμ1 hc
  obtain ⟨Rw, hRw⟩ :=
    regular_energy_momentum_bound_from_coordinate_bounds μ c Rz δ hδ
  refine ⟨Rw, ?_⟩
  intro s hs
  have hreg : s ∈ regularEnergyLocus μ c :=
    connectedComponentIn_subset (regularEnergyLocus μ c) (leftCollisionPoint μ) hs
  exact hRw s hreg (hRz s hs).1 (hRz s hs).2 (hsep s hs)
