-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.totalLength_le_freshTupleBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:51:14.152918+00:00
-- url     : https://prove2.me/submissions/aba854eb-1899-4488-9204-a5180aeb6750

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_expansionBlockCountBound_pos
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperTexts_top
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_le_of_mem_upperTexts
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_topLevel_le
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
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
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (hsl : IsMinimalFresh T W) :
    totalLength W ≤ freshTupleBound k (Fintype.card S) := by
  have hn := (topLevel_le hsl.1).trans (Nat.mul_le_mul_left k (Nat.sub_le (Fintype.card S) 1))
  have hword : ∀ l, (W l).length ≤
      expansionBlockCountBound k (Fintype.card S) ^ (k * Fintype.card S + 1) := by
    intro l
    by_cases hl : W l = []
    · simp [hl]
    · have hm : W l ∈ upperTexts W (topLevel W) := by
        rw [upperTexts_top]; exact mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ l, hl⟩)
      exact (length_le_of_mem_upperTexts hsl _ le_rfl hm).trans
        (Nat.pow_le_pow_right (expansionBlockCountBound_pos k (Fintype.card S)) (by omega))
  unfold totalLength freshTupleBound
  calc
    _ ≤ ∑ _ : Fin k, expansionBlockCountBound k (Fintype.card S) ^ (k * Fintype.card S + 1) :=
      sum_le_sum (fun l _ => hword l)
    _ = _ := by simp
end DeciSigma1.Holes.Fresh
