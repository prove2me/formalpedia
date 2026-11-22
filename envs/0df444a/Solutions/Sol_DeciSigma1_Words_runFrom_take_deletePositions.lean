-- Prove2me | solution 1 for DeciSigma1.Words.runFrom_take_deletePositions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:58:51.68214+00:00
-- url     : https://prove2.me/submissions/45cc5ec3-2425-4fed-885f-f31888f57d48

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_deletePositions_take
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_not_mem
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_mono
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_length
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_le_length
public import Theorems.Thm_DeciSigma1_Words_runFrom_deletePositions_take
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
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
namespace DeciSigma1.Words
theorem _root_.solution (T : Table α S k) (q : S) (w : List α)
    (hblock : ∀ j c, j < c → c ≤ w.length → (∀ p, j ≤ p → p < c → p ∈ D) →
      (j = 0 ∨ j - 1 ∉ D) → c ∉ D → runFrom T.step q (w.take j) = runFrom T.step q (w.take c))
    (hD : w.length ∉ D) (a : ℕ) :
    runFrom T.step q ((deletePositions w D).take a) =
        runFrom T.step q (w.take (greatestPreimage D a)) := by
  have key : ∀ a ≤ (deletePositions w D).length,
      runFrom T.step q ((deletePositions w D).take a) =
        runFrom T.step q (w.take (greatestPreimage D a)) := by
    intro a ha
    have hle := greatestPreimage_le_length w hD ha
    rw [← runFrom_deletePositions_take T q w hblock _ hle (Or.inr (Or.inl
        (greatestPreimage_not_mem a))),
      ← deletePositions_take w hle, retainedCount_greatestPreimage]
  rcases Nat.le_total a (deletePositions w D).length with ha | ha
  · exact key a ha
  · have hw : w.length ≤ greatestPreimage D a :=
      (greatestPreimage_length w hD).ge.trans (greatestPreimage_mono ha)
    have h := key _ le_rfl
    rw [greatestPreimage_length w hD, List.take_length, List.take_length] at h
    rw [List.take_of_length_le ha, List.take_of_length_le hw, h]
end DeciSigma1.Words
