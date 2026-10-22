-- Prove2me | solution 1 for BirkhoffGlobalSection.left_component_radial_norm_positive
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T10:07:06.654008+00:00
-- url     : https://prove2.me/submissions/c93e3e1f-174d-47a4-a143-467d26ee7ffc

import Mathlib
import Definitions.Def_BirkhoffGlobalSection

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ leftEnergyComponent μ c,
      0 < zNormSq s + wNormSq s := by
  intro s hs
  have hnonneg : 0 ≤ zNormSq s + wNormSq s := by
    dsimp [zNormSq, wNormSq]
    positivity
  by_contra h
  have hnorm : zNormSq s + wNormSq s = 0 :=
    le_antisymm (le_of_not_gt h) hnonneg
  have h0 : s 0 = 0 := by
    dsimp [zNormSq, wNormSq] at hnorm
    nlinarith [sq_nonneg (s 1), sq_nonneg (s 2), sq_nonneg (s 3)]
  have h1 : s 1 = 0 := by
    dsimp [zNormSq, wNormSq] at hnorm
    nlinarith [sq_nonneg (s 0), sq_nonneg (s 2), sq_nonneg (s 3)]
  have h2 : s 2 = 0 := by
    dsimp [zNormSq, wNormSq] at hnorm
    nlinarith [sq_nonneg (s 0), sq_nonneg (s 1), sq_nonneg (s 3)]
  have h3 : s 3 = 0 := by
    dsimp [zNormSq, wNormSq] at hnorm
    nlinarith [sq_nonneg (s 0), sq_nonneg (s 1), sq_nonneg (s 2)]
  have hreg : s ∈ regularEnergyLocus μ c :=
    connectedComponentIn_subset (regularEnergyLocus μ c)
      (leftCollisionPoint μ) hs
  have henergy : leviCivitaHamiltonian μ c s = 0 := hreg.1
  simp only [leviCivitaHamiltonian, zNormSq, wNormSq,
    secondCollisionDistanceSq, h0, h1, h2, h3] at henergy
  norm_num at henergy
  linarith
