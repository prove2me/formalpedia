-- Prove2me | solution 1 for BirkhoffGlobalSection.inner_lagrange_subcritical_circle_energy_positive
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T10:17:09.752604+00:00
-- url     : https://prove2.me/submissions/f5713ce0-6146-4af0-b279-a69f3fff95c8

import Mathlib.Tactic
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_realizes_first_critical_value
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_circle_hamiltonian_lower_bound

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ s : Phase,
        ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
          ((leviCivitaPosition μ s) 1) ^ 2 = r ^ 2 →
          0 < leviCivitaHamiltonian μ c s := by
  obtain ⟨L, hL, hval⟩ :=
    inner_lagrange_realizes_first_critical_value μ hμ0 hμ1
  let r : ℝ := L 0 + μ
  have hrpos : 0 < r := by dsimp [r]; linarith [hL.2.2.1]
  have hrone : r < 1 := by dsimp [r]; linarith [hL.2.2.2.1]
  refine ⟨r, hrpos, hrone, ?_⟩
  intro s heq
  have hcircle := inner_lagrange_circle_hamiltonian_lower_bound
    μ hμ0 hμ1 L hL s heq
  have hcomplex :
      ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
        ((leviCivitaPosition μ s) 1) ^ 2 = (2 * zNormSq s) ^ 2 := by
    dsimp [leviCivitaPosition, zNormSq]
    ring
  have hZpos : 0 < zNormSq s := by
    have hZnonneg : 0 ≤ zNormSq s := by dsimp [zNormSq]; positivity
    nlinarith [hcomplex, heq]
  have henergy : leviCivitaHamiltonian μ c s =
      leviCivitaHamiltonian μ 0 s + c * zNormSq s := by
    dsimp [leviCivitaHamiltonian]
    ring
  have hcpos : 0 < firstCriticalValue μ + c := by
    change -c < firstCriticalValue μ at hc
    linarith
  have hbound : zNormSq s * (firstCriticalValue μ + c) ≤
      leviCivitaHamiltonian μ c s := by
    rw [henergy, ← hval]
    nlinarith [hcircle]
  nlinarith [mul_pos hZpos hcpos]
