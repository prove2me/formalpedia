-- Prove2me | solution 1 for DeciSigma1.Words.greatestPreimage_union_Ico
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:47:18.211951+00:00
-- url     : https://prove2.me/submissions/40527dac-dadc-463a-b8ad-bd93aa00bbc2

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_not_mem
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_retainedCount
public import Theorems.Thm_DeciSigma1_Words_retainedCount_union_Ico_of_le
public import Theorems.Thm_DeciSigma1_Words_retainedCount_union_Ico_of_ge
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
variable {c δ : ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (hD : ∀ p ∈ D, p < c) (a : ℕ) :
    greatestPreimage (D ∪ Finset.Ico c (c + δ)) a =
      if greatestPreimage D a < c then greatestPreimage D a else greatestPreimage D a + δ := by
  have key : ∀ q, q ∉ D ∪ Finset.Ico c (c + δ) →
      retainedCount (D ∪ Finset.Ico c (c + δ)) q = a →
      greatestPreimage (D ∪ Finset.Ico c (c + δ)) a = q :=
          fun q hq h => h ▸ greatestPreimage_retainedCount hq
  split_ifs with h
  · refine key _ (fun hm => ?_) ?_
    · rcases Finset.mem_union.mp hm with h' | h'
      · exact greatestPreimage_not_mem a h'
      · have := (Finset.mem_Ico.mp h').1; omega
    · rw [retainedCount_union_Ico_of_le h.le, retainedCount_greatestPreimage]
  · refine key _ (fun hm => ?_) ?_
    · rcases Finset.mem_union.mp hm with h' | h'
      · have := hD _ h'; omega
      · have := (Finset.mem_Ico.mp h').2; omega
    · rw [retainedCount_union_Ico_of_ge hD (by omega), Nat.add_sub_cancel,
        retainedCount_greatestPreimage]
end DeciSigma1.Words
