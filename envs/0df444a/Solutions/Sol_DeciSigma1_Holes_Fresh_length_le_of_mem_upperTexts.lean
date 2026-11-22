-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.length_le_of_mem_upperTexts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:50:37.634981+00:00
-- url     : https://prove2.me/submissions/c89ccb7a-df91-4eb6-ad24-d4a24afdbd64

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_flatten_upperParse
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperParse_length_le_expansionBlockCountBound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_flatten_length_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_reversedBlocks_zero_length_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_getElem_reversedBlocks_mem_upperTexts
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
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
theorem _root_.solution (hsl : IsMinimalFresh T W) (t : ℕ) (ht : t ≤ topLevel W)
    {z : List α} (hz : z ∈ upperTexts W t) :
    z.length ≤ expansionBlockCountBound k (Fintype.card S) ^ (t + 1) := by
  induction t generalizing z with
  | zero =>
    obtain ⟨o, ho, rfl⟩ := mem_image.mp hz
    have hparse : (upperParse W 0 o).length ≤ expansionBlockCountBound k (Fintype.card S) :=
      upperParse_length_le_expansionBlockCountBound hsl ht (mem_image_of_mem _ ho)
    rw [← flatten_upperParse ho]
    have hbase := flatten_length_le (upperParse W 0 o) 1 (by
      intro x hx
      rw [upperParse, List.mem_reverse] at hx
      obtain ⟨d, hd, rfl⟩ := List.mem_iff_getElem.mp hx
      exact (reversedBlocks_zero_length_one ho hd).le)
    simpa using hbase.trans (by simpa using hparse)
  | succ t ih =>
    obtain ⟨o, ho, rfl⟩ := mem_image.mp hz
    have hparse : (upperParse W (t + 1) o).length ≤ expansionBlockCountBound k (Fintype.card S) :=
      upperParse_length_le_expansionBlockCountBound hsl ht (mem_image_of_mem _ ho)
    have hbase := flatten_length_le (upperParse W (t + 1) o)
      (expansionBlockCountBound k (Fintype.card S) ^ (t + 1)) (by
        intro x hx
        rw [upperParse, List.mem_reverse] at hx
        obtain ⟨d, hd, rfl⟩ := List.mem_iff_getElem.mp hx
        exact ih (by omega) (getElem_reversedBlocks_mem_upperTexts ho hd))
    rw [← flatten_upperParse ho]
    apply hbase.trans
    calc
      _ ≤ expansionBlockCountBound k (Fintype.card S) *
          expansionBlockCountBound k (Fintype.card S) ^ (t + 1) :=
        Nat.mul_le_mul_right _ hparse
      _ = _ := by rw [pow_succ _ (t + 1), Nat.mul_comm]
end DeciSigma1.Holes.Fresh
