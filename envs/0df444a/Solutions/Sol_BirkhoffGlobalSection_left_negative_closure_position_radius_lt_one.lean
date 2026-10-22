-- Prove2me | solution 1 for BirkhoffGlobalSection.left_negative_closure_position_radius_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T17:56:53.91752+00:00
-- url     : https://prove2.me/submissions/c86800ef-2abf-4d22-a1c3-3a225a337095

import Mathlib
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_subcritical_circle_energy_positive

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ ρ : ℝ, ρ < 1 ∧
      ∀ s ∈ closure
        (connectedComponentIn
          {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
            0 < secondCollisionDistanceSq t}
          (fun _ : Fin 4 => (0 : ℝ))),
        ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
          ((leviCivitaPosition μ s) 1) ^ 2 ≤ ρ := by
  obtain ⟨r, hrpos, hrone, hcircle⟩ :=
    inner_lagrange_subcritical_circle_energy_positive μ c hμ0 hμ1 hc
  let f : Phase → ℝ := fun s =>
    ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
      ((leviCivitaPosition μ s) 1) ^ 2
  let N : Set Phase :=
    {s | leviCivitaHamiltonian μ c s < 0 ∧
      0 < secondCollisionDistanceSq s}
  let C : Set Phase := connectedComponentIn N (fun _ : Fin 4 => (0 : ℝ))
  have hfcont : Continuous f := by
    dsimp [f, leviCivitaPosition]
    fun_prop
  have hK0 : leviCivitaHamiltonian μ c
      (fun _ : Fin 4 => (0 : ℝ)) = -(1 - μ) / 2 := by
    dsimp [leviCivitaHamiltonian, wNormSq, zNormSq,
      secondCollisionDistanceSq]
    norm_num <;> ring
  have hzeroN : (fun _ : Fin 4 => (0 : ℝ)) ∈ N := by
    constructor
    · rw [hK0]
      linarith
    · norm_num [secondCollisionDistanceSq]
  have hbase : (fun _ : Fin 4 => (0 : ℝ)) ∈ C :=
    mem_connectedComponentIn hzeroN
  have hfbase : f (fun _ : Fin 4 => (0 : ℝ)) = 0 := by
    dsimp [f, leviCivitaPosition]
    ring
  have hCbound : ∀ s ∈ C, f s ≤ r ^ 2 := by
    intro s hs
    by_contra h
    have hgt : r ^ 2 < f s := lt_of_not_ge h
    have himage := (isPreconnected_connectedComponentIn :
      IsPreconnected C).intermediate_value hbase hs hfcont.continuousOn
    have hmem : r ^ 2 ∈ Set.Icc (f (fun _ : Fin 4 => (0 : ℝ))) (f s) := by
      rw [hfbase]
      exact ⟨sq_nonneg r, le_of_lt hgt⟩
    obtain ⟨t, ht, hft⟩ := himage hmem
    have htneg : leviCivitaHamiltonian μ c t < 0 :=
      (connectedComponentIn_subset N (fun _ => 0) ht).1
    have htpos : 0 < leviCivitaHamiltonian μ c t :=
      hcircle t (by simpa only [f] using hft)
    linarith
  refine ⟨r ^ 2, by nlinarith, ?_⟩
  intro s hs
  change f s ≤ r ^ 2
  have hclosed : IsClosed {t : Phase | f t ≤ r ^ 2} :=
    isClosed_le hfcont continuous_const
  exact (closure_minimal hCbound hclosed) hs
