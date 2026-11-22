-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.occurrenceCuts_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:37:59.921998+00:00
-- url     : https://prove2.me/submissions/7b1d2ae0-b103-49f0-8d99-b91fe221e9ec

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_relativeCuts
public import Theorems.Thm_DeciSigma1_Holes_Fresh_occurrenceText_length
public import Theorems.Thm_DeciSigma1_Holes_Fresh_take_start_append_occurrenceText
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_take
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperOcc_spec
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
theorem _root_.solution {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) : occurrenceCuts W t o =
      insert (occurrenceText W o).length
          (relativeAnchors W t ((W o.1).take o.2.1) (occurrenceText W o)) := by
  have hspec := upperOcc_spec ho
  have hlen := occurrenceText_length ho
  have hpre : ((W o.1).take o.2.1).length = o.2.1 := by simp; omega
  have happ := take_start_append_occurrenceText ho
  ext p
  simp only
      [occurrenceCuts, mem_relativeCuts, mem_insert, relativeAnchors, mem_filter, mem_Icc, hpre,
          happ]
  constructor
  · rintro ⟨hp, hpe, hpa⟩
    by_cases hlast : p = (occurrenceText W o).length
    · exact Or.inl hlast
    · right
      refine ⟨⟨by omega, by omega⟩, (mem_contextAnchors_take (by omega)).mpr ?_⟩
      rcases mem_insert.mp hpa with h | h
      · omega
      · exact h
  · rintro (rfl | ⟨⟨hp, hpz⟩, hctx⟩)
    · rw [hlen]
      exact ⟨by omega, by omega, by convert hspec.2.2.1 using 1; omega⟩
    · exact ⟨by omega, by omega, mem_insert_of_mem ((mem_contextAnchors_take (by omega)).mp hctx)⟩
end DeciSigma1.Holes.Fresh
