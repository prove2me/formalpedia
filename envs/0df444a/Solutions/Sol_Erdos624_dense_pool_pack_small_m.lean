-- Prove2me | solution 1 for Erdos624.dense_pool_pack_small_m
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T09:18:50.941786+00:00
-- url     : https://prove2.me/submissions/26cf8a6c-527d-4640-89fa-196c0831f099

import Mathlib

set_option maxHeartbeats 8000000

/-!
Honesty: does not settle PAIR / Step 17 / #624.
Credit: GPT 6.1 Sol -> Ethan Cheung; Lean by Grok Bot (Oct 24 2026).
Small-m branch of dense-pool circuit packing: m ≤ 2^30 a^7 ⇒ m^4 ≤ 2^120 a^28 n^3.
-/

namespace E624R9

open Finset BigOperators Nat Classical

def packConst : ℕ := 2 ^ 120

lemma pack_of_small_m (a m n : ℕ) (_ha : 1 ≤ a) (hn : 1 ≤ n)
    (hm : m ≤ 2 ^ 30 * a ^ 7) :
    m ^ 4 ≤ packConst * a ^ 28 * n ^ 3 := by
  unfold packConst
  have h1 : m ^ 4 ≤ (2 ^ 30 * a ^ 7) ^ 4 := Nat.pow_le_pow_left hm 4
  have h2 : (2 ^ 30 * a ^ 7) ^ 4 = 2 ^ 120 * a ^ 28 := by
    calc (2 ^ 30 * a ^ 7) ^ 4
        = (2 ^ 30) ^ 4 * (a ^ 7) ^ 4 := mul_pow _ _ 4
      _ = 2 ^ 120 * a ^ 28 := by rw [← pow_mul, ← pow_mul]
  have h3 : 2 ^ 120 * a ^ 28 ≤ 2 ^ 120 * a ^ 28 * n ^ 3 := by
    have : 1 ≤ n ^ 3 := Nat.one_le_pow 3 n hn
    exact Nat.le_mul_of_pos_right _ this
  exact le_trans h1 (le_trans (le_of_eq h2) h3)

end E624R9

namespace Erdos624

open Finset BigOperators

theorem dense_pool_pack_small_m
    {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    {k : ℕ} (L : Finset U → Finset C) (_hLcap : ∀ A, #(L A) ≤ 2)
    (M : Finset C) (pool : C → Finset U)
    (_lab : C → U → (Fin (k - 1) → ZMod 2)) (a : ℕ)
    (ha : 1 ≤ a)
    (_hPool : ∀ u ∈ M, a * #(pool u) ≥ Fintype.card U)
    (_hCompat : ∀ u ∈ M,
      ∀ A : Finset U, A ⊆ pool u →
        (A.Nonempty ∧ (∑ x ∈ A, _lab u x) = 0 ∧
          ∀ ⦃S : Finset U⦄, S ⊆ A → S.Nonempty → S ≠ A →
            ∑ x ∈ S, _lab u x ≠ 0) →
        #A ≤ 8 → u ∈ L A)
    (hn : 1 ≤ Fintype.card U)
    (hm : #M ≤ 2 ^ 30 * a ^ 7) :
    (#M) ^ 4 ≤ 2 ^ 120 * a ^ 28 * (Fintype.card U) ^ 3 := by
  simpa [E624R9.packConst] using
    E624R9.pack_of_small_m a (#M) (Fintype.card U) ha hn hm

end Erdos624

open Finset BigOperators

theorem solution
    {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    {k : ℕ} (L : Finset U → Finset C) (hLcap : ∀ A, #(L A) ≤ 2)
    (M : Finset C) (pool : C → Finset U)
    (lab : C → U → (Fin (k - 1) → ZMod 2)) (a : ℕ)
    (ha : 1 ≤ a)
    (hPool : ∀ u ∈ M, a * #(pool u) ≥ Fintype.card U)
    (hCompat : ∀ u ∈ M,
      ∀ A : Finset U, A ⊆ pool u →
        (A.Nonempty ∧ (∑ x ∈ A, lab u x) = 0 ∧
          ∀ ⦃S : Finset U⦄, S ⊆ A → S.Nonempty → S ≠ A →
            ∑ x ∈ S, lab u x ≠ 0) →
        #A ≤ 8 → u ∈ L A)
    (hn : 1 ≤ Fintype.card U)
    (hm : #M ≤ 2 ^ 30 * a ^ 7) :
    (#M) ^ 4 ≤ 2 ^ 120 * a ^ 28 * (Fintype.card U) ^ 3 :=
  Erdos624.dense_pool_pack_small_m L hLcap M pool lab a ha hPool hCompat hn hm

#print axioms solution
