-- Prove2me | solution 1 for BirkhoffGlobalSection.regular_energy_momentum_bound_from_coordinate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T08:18:50.5368+00:00
-- url     : https://prove2.me/submissions/68b038bd-e67f-4a2f-864d-e7f91c2591e0

import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_BirkhoffGlobalSection_regular_energy_coefficients_bounded_on_box
import Theorems.Thm_BirkhoffGlobalSection_quadratic_energy_coordinate_bound

open BirkhoffGlobalSection

theorem solution (μ c Rz δ : ℝ) (hδ : 0 < δ) :
    ∃ Rw : ℝ, ∀ s ∈ regularEnergyLocus μ c,
      |s 0| ≤ Rz → |s 1| ≤ Rz →
      δ ≤ Real.sqrt (secondCollisionDistanceSq s) →
      |s 2| ≤ Rw ∧ |s 3| ≤ Rw := by
  obtain ⟨M, hM, hcoeff⟩ :=
    regular_energy_coefficients_bounded_on_box μ c Rz δ hδ
  refine ⟨4 * M + 4, ?_⟩
  intro s hs hx hy hd
  obtain ⟨hA, hB, hK⟩ := hcoeff s hs hx hy hd
  have hzero : leviCivitaHamiltonian μ c s = 0 := hs.1
  have heq : ((s 2) ^ 2 + (s 3) ^ 2) / 2 +
      (-(2 * zNormSq s + μ) * s 1) * s 2 +
      ((2 * zNormSq s - μ) * s 0) * s 3 +
      (c * zNormSq s - (1 - μ) / 2 -
        μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s)) = 0 := by
    unfold leviCivitaHamiltonian wNormSq at hzero
    simp only [div_eq_mul_inv] at hzero ⊢
    linear_combination hzero
  exact quadratic_energy_coordinate_bound M
    (-(2 * zNormSq s + μ) * s 1)
    ((2 * zNormSq s - μ) * s 0)
    (c * zNormSq s - (1 - μ) / 2 -
      μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s))
    (s 2) (s 3) hM hA hB hK heq
