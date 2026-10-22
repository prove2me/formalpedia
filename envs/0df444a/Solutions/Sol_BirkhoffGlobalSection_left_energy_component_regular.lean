-- Prove2me | solution 1 for BirkhoffGlobalSection.left_energy_component_regular
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T18:18:51.841426+00:00
-- url     : https://prove2.me/submissions/3f5f5647-e14b-4cca-abd8-91566d0dd8fe

import Mathlib.Tactic.Positivity
import Theorems.Thm_BirkhoffGlobalSection_leviCivita_regularAt_left_collision
import Theorems.Thm_BirkhoffGlobalSection_leviCivita_regularAt_collisionFree_subcritical_energy

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ leftEnergyComponent μ c,
      fderiv ℝ (leviCivitaHamiltonian μ c) s ≠ 0 := by
  intro s hs
  have hreg : s ∈ regularEnergyLocus μ c :=
    connectedComponentIn_subset (regularEnergyLocus μ c) (leftCollisionPoint μ) hs
  have hK : leviCivitaHamiltonian μ c s = 0 := hreg.1
  have hD : 0 < secondCollisionDistanceSq s := hreg.2
  have hznonneg : 0 ≤ zNormSq s := by
    unfold zNormSq
    positivity
  by_cases hz : zNormSq s = 0
  · exact leviCivita_regularAt_left_collision μ c hμ1 s hK hz
  · have hzpos : 0 < zNormSq s := lt_of_le_of_ne hznonneg (Ne.symm hz)
    exact leviCivita_regularAt_collisionFree_subcritical_energy
      μ c hμ0 hμ1 hc s hK hD hzpos
