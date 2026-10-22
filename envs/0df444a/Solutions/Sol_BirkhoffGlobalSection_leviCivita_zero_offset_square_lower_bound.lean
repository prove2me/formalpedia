-- Prove2me | solution 1 for BirkhoffGlobalSection.leviCivita_zero_offset_square_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T07:30:35.807786+00:00
-- url     : https://prove2.me/submissions/19d0ced7-22a3-4640-aab5-ba1521045396

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_BirkhoffGlobalSection

open BirkhoffGlobalSection

theorem solution (μ : ℝ) (s : Phase) :
    -(zNormSq s) *
        (((leviCivitaPosition μ s) 0) ^ 2 +
          ((leviCivitaPosition μ s) 1) ^ 2) / 2 -
      (1 - μ) / 2 -
      μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s) ≤
        leviCivitaHamiltonian μ 0 s := by
  let Z : ℝ := zNormSq s
  let R : ℝ := -Z *
      (((leviCivitaPosition μ s) 0) ^ 2 +
        ((leviCivitaPosition μ s) 1) ^ 2) / 2 -
      (1 - μ) / 2 - μ * Z / Real.sqrt (secondCollisionDistanceSq s)
  have hidentity : leviCivitaHamiltonian μ 0 s = R +
      (s 2 - (2 * Z + μ) * s 1) ^ 2 / 2 +
      (s 3 + (2 * Z - μ) * s 0) ^ 2 / 2 := by
    dsimp [R, Z, leviCivitaHamiltonian, leviCivitaPosition,
      zNormSq, wNormSq]
    ring
  change R ≤ leviCivitaHamiltonian μ 0 s
  rw [hidentity]
  nlinarith [sq_nonneg (s 2 - (2 * Z + μ) * s 1),
    sq_nonneg (s 3 + (2 * Z - μ) * s 0)]
