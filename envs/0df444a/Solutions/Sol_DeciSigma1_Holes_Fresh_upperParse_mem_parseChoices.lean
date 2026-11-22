-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.upperParse_mem_parseChoices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:39:02.466801+00:00
-- url     : https://prove2.me/submissions/c54a123a-d3c5-4439-90fd-46c9fbe6d7a8

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperParse_eq_parseText
public import Theorems.Thm_DeciSigma1_Holes_Fresh_occurrenceCuts_eq
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_crossBoundaryMarkerEnds_subset_prefixOccurrenceCuts
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_relativeAnchors_eq
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
theorem _root_.solution {t : ℕ} {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) :
    upperParse W t o ∈ parseChoices W t (occurrenceText W o) := by
  rw [upperParse_eq_parseText ho, occurrenceCuts_eq ho]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have hrel : relativeAnchors W 0 ((W o.1).take o.2.1) (occurrenceText W o) =
        contextAnchors W 0 (occurrenceText W o) := by
      ext p
      simp only [relativeAnchors, contextAnchors, mem_filter, mem_Icc, List.length_append]
      omega
    rw [hrel]
    exact mem_image.mpr ⟨∅, mem_powerset.mpr (empty_subset _), by simp⟩
  · rw [relativeAnchors_eq ht]
    exact mem_image.mpr
        ⟨_, mem_powerset.mpr (crossBoundaryMarkerEnds_subset_prefixOccurrenceCuts _ _), rfl⟩
end DeciSigma1.Holes.Fresh
