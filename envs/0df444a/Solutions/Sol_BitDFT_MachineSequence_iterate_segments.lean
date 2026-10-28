-- Prove2me | solution 1 for BitDFT.MachineSequence.iterate_segments
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T22:53:44.858989+00:00
-- url     : https://prove2.me/submissions/c84ded2d-441a-4b3b-ae03-0e74ae9b2728

import Definitions.Def_BitDFT_MachineSequence

set_option autoImplicit false

theorem solution {α : Type} (f : α → α) (cfg : ℕ → α) (cost : ℕ → ℕ)
    (hsegment : ∀ i, f^[cost i] (cfg i) = cfg (i + 1)) (n : ℕ) :
    f^[∑ i ∈ Finset.range n, cost i] (cfg 0) = cfg n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        f^[∑ i ∈ Finset.range n, cost i + cost n] (cfg 0) =
            f^[cost n] (f^[∑ i ∈ Finset.range n, cost i] (cfg 0)) := by
              rw [show (∑ i ∈ Finset.range n, cost i) + cost n =
                  cost n + ∑ i ∈ Finset.range n, cost i by omega,
                Function.iterate_add_apply]
        _ = f^[cost n] (cfg n) := by rw [ih]
        _ = cfg (n + 1) := hsegment n
