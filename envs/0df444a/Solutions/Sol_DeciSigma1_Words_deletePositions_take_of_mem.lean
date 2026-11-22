-- Prove2me | solution 1 for DeciSigma1.Words.deletePositions_take_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:46:31.825862+00:00
-- url     : https://prove2.me/submissions/ac83066b-311f-4853-80d5-5ecb6f04d9f8

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_deletePositions_take_succ

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (w : List α) {j c : ℕ} (hjc : j ≤ c)
    (h : ∀ p, j ≤ p → p < c → p ∈ D) : deletePositions (w.take c) D =
        deletePositions (w.take j) D := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjc
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc, deletePositions_take_succ, if_pos (h _ (by omega) (by omega)),
        List.append_nil,
      ih (by omega) (fun p hp hpc => h p hp (by omega))]
end DeciSigma1.Words
