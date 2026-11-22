-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.take_depthCut_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:59:08.518815+00:00
-- url     : https://prove2.me/submissions/49f90dee-ea3d-4e05-af12-1fd23c699f96

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_lt
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
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {t : ℕ} {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d : ℕ}
    (hd : d ≤ lowerBlockCount W t o) :
    (W o.1).take (depthCut W t o d) ++ ((reversedBlocks W t o).take d).reverse.flatten =
      (W o.1).take o.2.2 := by
  induction d with
  | zero => simp [depthCut, depthCutAt]
  | succ d ih =>
    have hdl : d < (reversedBlocks W t o).length := by simp; omega
    have hlt := depthCut_lt ho (by omega : d < lowerBlockCount W t o)
    rw [List.take_add_one, List.getElem?_eq_getElem hdl, Option.toList_some,
      List.reverse_append, List.reverse_singleton, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil, ← List.append_assoc,
      getElem_reversedBlocks]
    have heq : (W o.1).take (depthCut W t o (d + 1)) ++
        ((W o.1).drop (depthCut W t o (d + 1))).take
          (depthCut W t o d - depthCut W t o (d + 1)) =
        (W o.1).take (depthCut W t o d) := by
      rw [← List.take_add]; congr 1; omega
    rw [heq]
    exact ih (by omega)
end DeciSigma1.Holes.Fresh
