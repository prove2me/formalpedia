-- Prove2me | solution 1 for CollectiveDFS.exchange_pauli
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:02:48.829203+00:00
-- url     : https://prove2.me/submissions/ea586a68-2ed9-4b25-8948-8cbaefbd929c

import Mathlib
import Definitions.Def_CollectiveDFS_exchange
import Definitions.Def_CollectiveDFS_pauli
import Definitions.Def_CollectiveDFS_onWire

open QAlgorithms

namespace Aux_CDFS_exch
open CollectiveDFS

lemma prod_entry {n : ℕ} (a b : Fin n) (hab : a ≠ b) (A B : Matrix Bool Bool ℂ)
    (x y : Qubits n) :
    (onWire a A * onWire b B) x y =
      if (∀ k, k ≠ a → k ≠ b → x k = y k) then A (x a) (y a) * B (x b) (y b) else 0 := by
  rw [Matrix.mul_apply]
  by_cases hc : ∀ k, k ≠ a → k ≠ b → x k = y k
  · rw [if_pos hc, Finset.sum_eq_single (Function.update x a (y a))]
    · simp only [onWire, Matrix.of_apply]
      have h1 : ∀ k, k ≠ a → x k = Function.update x a (y a) k := by
        intro k hk; rw [Function.update_of_ne hk]
      have h2 : ∀ k, k ≠ b → Function.update x a (y a) k = y k := by
        intro k hk
        by_cases hka : k = a
        · subst hka; rw [Function.update_self]
        · rw [Function.update_of_ne hka]; exact hc k hka hk
      rw [if_pos h1, if_pos h2, Function.update_self, Function.update_of_ne (Ne.symm hab)]
    · intro z _ hz
      simp only [onWire, Matrix.of_apply]
      by_cases h1 : ∀ k, k ≠ a → x k = z k
      · by_cases h2 : ∀ k, k ≠ b → z k = y k
        · exfalso; apply hz
          funext k
          by_cases hka : k = a
          · subst hka; rw [Function.update_self]; exact h2 k hab
          · rw [Function.update_of_ne hka]; exact (h1 k hka).symm
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro z _
    simp only [onWire, Matrix.of_apply]
    by_cases h1 : ∀ k, k ≠ a → x k = z k
    · by_cases h2 : ∀ k, k ≠ b → z k = y k
      · exfalso; apply hc
        intro k hka hkb
        exact (h1 k hka).trans (h2 k hkb)
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

end Aux_CDFS_exch

open CollectiveDFS Aux_CDFS_exch in
theorem solution (n : ℕ) (a b : Fin n) (hab : a ≠ b) :
    exchange a b =
      (1 / 2 : ℂ) • (1 + ∑ α : Fin 3, onWire a (pauli α) * onWire b (pauli α)) := by
  ext x y
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply]
  simp only [prod_entry a b hab]
  by_cases hc : ∀ k, k ≠ a → k ≠ b → x k = y k
  · simp only [if_pos hc]
    have e1 : (x = y ∘ Equiv.swap a b) ↔ (x a = y b ∧ x b = y a) := by
      constructor
      · intro h
        rw [h]
        simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
      · rintro ⟨h1, h2⟩
        funext k
        by_cases hka : k = a
        · subst hka; simp [Equiv.swap_apply_left, h1]
        · by_cases hkb : k = b
          · subst hkb; simp [Equiv.swap_apply_right, h2]
          · simp [Equiv.swap_apply_of_ne_of_ne hka hkb, hc k hka hkb]
    have e2 : (x = y) ↔ (x a = y a ∧ x b = y b) := by
      constructor
      · intro h; rw [h]; exact ⟨rfl, rfl⟩
      · rintro ⟨h1, h2⟩
        funext k
        by_cases hka : k = a
        · subst hka; exact h1
        · by_cases hkb : k = b
          · subst hkb; exact h2
          · exact hc k hka hkb
    simp only [exchange, Matrix.of_apply, Matrix.one_apply, e1, e2]
    cases x a <;> cases x b <;> cases y a <;> cases y b <;>
      simp [pauli, pauliX, pauliY, pauliZ, Fin.sum_univ_three] <;> ring_nf <;>
      simp [Complex.I_sq] <;> norm_num
  · simp only [if_neg hc, Finset.sum_const_zero, add_zero]
    have h1 : ¬ (x = y ∘ Equiv.swap a b) := by
      intro h; apply hc; intro k hka hkb
      rw [h]; simp [Equiv.swap_apply_of_ne_of_ne hka hkb]
    have h2 : ¬ (x = y) := by
      intro h; apply hc; intro k _ _; rw [h]
    simp [exchange, Matrix.one_apply, h1, h2]
