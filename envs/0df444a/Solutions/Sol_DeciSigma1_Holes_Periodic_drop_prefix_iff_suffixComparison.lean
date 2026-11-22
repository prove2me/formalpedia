-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.drop_prefix_iff_suffixComparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:43:49.776501+00:00
-- url     : https://prove2.me/submissions/52456b3b-398c-4c62-82a2-a7390c39a391

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_coordinate
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_start
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_coordinate
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_start
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_stop
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution {y z : List α} {b a : ℕ} :
    y.drop b <+: z.drop a ↔ SuffixComparison y b z a := by
  rw [List.prefix_iff_getElem?]
  constructor
  · intro h n hn
    have := h n (by simp; omega)
    rw [List.getElem?_drop] at this
    rw [this, List.getElem_drop, List.getElem?_eq_getElem hn]
  · intro h n hn
    simp only [List.length_drop] at hn
    rw [List.getElem?_drop, ← h n (by omega), List.getElem_drop, List.getElem?_eq_getElem]
end DeciSigma1.Holes.Periodic
