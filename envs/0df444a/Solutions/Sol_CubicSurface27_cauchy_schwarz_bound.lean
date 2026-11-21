-- Prove2me | solution 1 for CubicSurface27.cauchy_schwarz_bound
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T01:33:17.259216+00:00
-- url     : https://prove2.me/submissions/61ede994-fc77-4be1-867b-c29fe90c706d

import Mathlib
open Finset

theorem solution (a : ℤ) (b : Fin 6 → ℤ)
    (ha : 0 < a) (hb : ∀ i, 0 ≤ b i)
    (hself : a ^ 2 - ∑ i : Fin 6, (b i) ^ 2 = -1)
    (hadj : 3 * a - ∑ i : Fin 6, b i = 1) :
    a < 3 := by
  have hQ : ∑ i : Fin 6, (b i) ^ 2 = a ^ 2 + 1 := by linarith
  have hS : ∑ i : Fin 6, b i = 3 * a - 1 := by linarith
  have hcs : (∑ i : Fin 6, b i) ^ 2 ≤ 6 * ∑ i : Fin 6, (b i) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 6))) (f := b)
    simpa using h
  rw [hS, hQ] at hcs
  nlinarith [hcs]
