-- Prove2me | solution 1 for Erdos624.dense_pool_circuit_packing_small
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T05:58:36.905208+00:00
-- url     : https://prove2.me/submissions/958eda43-fc02-4e58-82e6-d8c6c399938f

import Mathlib
open Finset BigOperators


/-- Dense-pool circuit packing, small-m branch (Sol Round 9).
If `#M ≤ 2^{30} a^7` with dense pools and short-circuit compatibility,
then `m^4 ≤ 2^{120} a^{28} n^3`. Does not settle PAIR / #624. -/
theorem solution
    {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    {k : ℕ} (L : Finset U → Finset C) (hLcap : ∀ A, #(L A) ≤ 2)
    (M : Finset C) (pool : C → Finset U) (lab : C → U → (Fin (k - 1) → ZMod 2)) (a : ℕ)
    (ha : 1 ≤ a)
    (hPool : ∀ u ∈ M, a * #(pool u) ≥ Fintype.card U)
    (hCompat : ∀ u ∈ M,
      ∀ A : Finset U, A ⊆ pool u → (A.Nonempty ∧ (∑ x ∈ A, lab u x) = 0 ∧
        ∀ ⦃S : Finset U⦄, S ⊆ A → S.Nonempty → S ≠ A → ∑ x ∈ S, lab u x ≠ 0) → #A ≤ 8 → u ∈ L A)
    (hn : 1 ≤ Fintype.card U)
    (hm : #M ≤ 2 ^ 30 * a ^ 7) :
    (#M) ^ 4 ≤ 2 ^ 120 * a ^ 28 * (Fintype.card U) ^ 3 := by
  have h1 : (#M) ^ 4 ≤ (2 ^ 30 * a ^ 7) ^ 4 := Nat.pow_le_pow_left hm 4
  have h2 : 1 ≤ (Fintype.card U) ^ 3 := Nat.one_le_pow _ _ hn
  calc (#M) ^ 4 ≤ (2 ^ 30 * a ^ 7) ^ 4 := h1
    _ = 2 ^ 120 * a ^ 28 := by ring
    _ ≤ 2 ^ 120 * a ^ 28 * (Fintype.card U) ^ 3 := Nat.le_mul_of_pos_right _ h2

