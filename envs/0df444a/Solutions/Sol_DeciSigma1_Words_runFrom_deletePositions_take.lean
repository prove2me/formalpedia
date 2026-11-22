-- Prove2me | solution 1 for DeciSigma1.Words.runFrom_deletePositions_take
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:51:16.317372+00:00
-- url     : https://prove2.me/submissions/ab5720a0-9c98-4894-a387-048592d318fd

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_deletePositions_take_succ
public import Theorems.Thm_DeciSigma1_Words_deletePositions_take_of_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_append
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.deletePositions_empty

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (T : Table α S k) (q : S) (w : List α)
    (hblock : ∀ j c, j < c → c ≤ w.length → (∀ p, j ≤ p → p < c → p ∈ D) →
      (j = 0 ∨ j - 1 ∉ D) → c ∉ D → runFrom T.step q (w.take j) = runFrom T.step q (w.take c))
    (c : ℕ) (hc : c ≤ w.length) (hint : c = 0 ∨ c ∉ D ∨ c - 1 ∉ D) :
    runFrom T.step q (deletePositions (w.take c) D) = runFrom T.step q (w.take c) := by
  classical
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases c with _ | c₀
    · simp
    by_cases hc₀ : c₀ ∈ D
    · have hcD : c₀ + 1 ∉ D := by
        rcases hint with h | h | h
        · omega
        · exact h
        · exact absurd hc₀ (by simpa using h)
      have hex : ∃ j, j ≤ c₀ ∧ ∀ p, j ≤ p → p < c₀ + 1 → p ∈ D :=
        ⟨c₀, le_rfl, fun p hp hpc => by rwa [show p = c₀ by omega]⟩
      obtain ⟨hjc, hjD⟩ := Nat.find_spec hex
      set j := Nat.find hex
      have hjmin : j = 0 ∨ j - 1 ∉ D := by
        by_contra hcon
        push Not at hcon
        have := Nat.find_min' hex (m := j - 1) ⟨by omega, fun p hp hpc => by
          rcases Nat.eq_or_lt_of_le hp with h | h
          · rw [← h]; exact hcon.2
          · exact hjD p (by omega) hpc⟩
        omega
      rw [deletePositions_take_of_mem w (show j ≤ c₀ + 1 by omega) hjD,
        ih j (by omega) (by omega) (by rcases hjmin with h | h; · left; exact h
                                       · right; right; exact h),
        hblock j (c₀ + 1) (by omega) hc hjD hjmin hcD]
    · rw [deletePositions_take_succ, if_neg hc₀, List.take_add_one, runFrom_append,
        runFrom_append, ih c₀ (by omega) (by omega) (Or.inr (Or.inl hc₀))]
end DeciSigma1.Words
