-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.text_depthCut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:32:26.634809+00:00
-- url     : https://prove2.me/submissions/f1fe140b-3138-40ed-b45b-b93504270d8e

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_lt
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_lt_of_lt
public import Theorems.Thm_DeciSigma1_Holes_Fresh_getElem_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
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
attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks
attribute [local simp] DeciSigma1.Holes.Fresh.length_upperSeq
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
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
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d d' : ℕ} (hdd : d ≤ d')
    (hd' : d' ≤ lowerBlockCount W t o) :
    ((W o.1).drop (depthCut W t o d')).take (depthCut W t o d - depthCut W t o d') =
      (((reversedBlocks W t o).take d').drop d).reverse.flatten := by
  induction d', hdd using Nat.le_induction with
  | base =>
    simp only [Nat.sub_self, List.take_zero]
    rw [List.drop_of_length_le (by simp)]; rfl
  | succ d' hdd ih =>
    have hlt := depthCut_lt ho (show d' < lowerBlockCount W t o by omega)
    have hle : depthCut W t o d' ≤ depthCut W t o d := by
      rcases Nat.eq_or_lt_of_le hdd with h | h
      · rw [h]
      · exact (depthCut_lt_of_lt ho h (by omega)).le
    have hd'r : d' < (reversedBlocks W t o).length := by simp; omega
    rw [show depthCut W t o d - depthCut W t o (d' + 1) =
        (depthCut W t o d' - depthCut W t o (d' + 1)) + (depthCut W t o d - depthCut W t o d')
        by omega, List.take_add, List.drop_drop,
      show depthCut W t o (d' + 1) + (depthCut W t o d' - depthCut W t o (d' + 1)) =
        depthCut W t o d' by omega, ih (by omega), List.take_add_one,
      List.getElem?_eq_getElem hd'r, Option.toList_some,
      List.drop_append_of_le_length (by simp; omega), List.reverse_append,
      List.reverse_singleton, List.singleton_append, List.flatten_cons, getElem_reversedBlocks]
end DeciSigma1.Holes.Fresh
