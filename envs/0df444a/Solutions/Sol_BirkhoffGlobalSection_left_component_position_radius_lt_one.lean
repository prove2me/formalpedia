-- Prove2me | solution 1 for BirkhoffGlobalSection.left_component_position_radius_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T08:28:25.180573+00:00
-- url     : https://prove2.me/submissions/3b0b5746-dcf9-4661-9942-b0573fd923a6

import Mathlib
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_subcritical_circle_forbidden

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ ρ : ℝ, ρ < 1 ∧ ∀ s ∈ leftEnergyComponent μ c,
      ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
        ((leviCivitaPosition μ s) 1) ^ 2 ≤ ρ := by
  obtain ⟨r, hrpos, hrone, hforbid⟩ :=
    inner_lagrange_subcritical_circle_forbidden μ c hμ0 hμ1 hc
  let f : Phase → ℝ := fun s =>
    ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
      ((leviCivitaPosition μ s) 1) ^ 2
  have hfcont : Continuous f := by
    dsimp [f, leviCivitaPosition]
    fun_prop
  have hbase_reg : leftCollisionPoint μ ∈ regularEnergyLocus μ c := by
    change leviCivitaHamiltonian μ c (leftCollisionPoint μ) = 0 ∧
      0 < secondCollisionDistanceSq (leftCollisionPoint μ)
    constructor
    · have hμ : 0 ≤ 1 - μ := by linarith
      dsimp [leviCivitaHamiltonian, leftCollisionPoint, wNormSq, zNormSq]
      simp only [Real.sq_sqrt hμ]
      ring
    · norm_num [secondCollisionDistanceSq, leftCollisionPoint]
  have hbase : leftCollisionPoint μ ∈ leftEnergyComponent μ c := by
    exact mem_connectedComponentIn hbase_reg
  have hfbase : f (leftCollisionPoint μ) = 0 := by
    dsimp [f, leviCivitaPosition, leftCollisionPoint]
    ring
  refine ⟨r ^ 2, by nlinarith, ?_⟩
  intro s hs
  change f s ≤ r ^ 2
  by_contra hlt
  have hgt : r ^ 2 < f s := lt_of_not_ge hlt
  have himage := (isPreconnected_connectedComponentIn :
    IsPreconnected (leftEnergyComponent μ c)).intermediate_value
      hbase hs (hfcont.continuousOn)
  have hmem : r ^ 2 ∈ Set.Icc (f (leftCollisionPoint μ)) (f s) := by
    rw [hfbase]
    exact ⟨sq_nonneg r, le_of_lt hgt⟩
  obtain ⟨t, ht, hft⟩ := himage hmem
  have htreg : t ∈ regularEnergyLocus μ c :=
    connectedComponentIn_subset (regularEnergyLocus μ c) (leftCollisionPoint μ) ht
  exact hforbid t htreg (by simpa only [f] using hft)
