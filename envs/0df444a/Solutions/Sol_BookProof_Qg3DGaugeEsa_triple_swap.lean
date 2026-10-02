-- Prove2me | solution 1 for BookProof.Qg3DGaugeEsa.triple_swap
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T16:44:54.088313+00:00
-- url     : https://prove2.me/submissions/d9a7ea90-0f89-4548-ac19-7457bbd65932

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Fin

open scoped BigOperators

-- Target: BookProof.Qg3DGaugeEsa.triple_swap
-- https://prove2.me/theorems/0eab5f6a-055c-4742-a8c0-f1e335963604
-- Proof reorganizes the same finite sum, first exchanging the two inner sums,
-- then exchanging the outer two sums.
theorem solution {α : Type*} [AddCommMonoid α] (F : Fin 64 → Fin 84 → Fin 84 → α) :
    ∑ i : Fin 84, ∑ j : Fin 84, ∑ m : Fin 64, F m i j
      = ∑ m : Fin 64, ∑ i : Fin 84, ∑ j : Fin 84, F m i j := by
  calc
    (∑ i : Fin 84, ∑ j : Fin 84, ∑ m : Fin 64, F m i j)
        = ∑ i : Fin 84, ∑ m : Fin 64, ∑ j : Fin 84, F m i j := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
    _ = ∑ m : Fin 64, ∑ i : Fin 84, ∑ j : Fin 84, F m i j := Finset.sum_comm
