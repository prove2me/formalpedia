-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.upperTexts_subset_parseBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:38:00.601379+00:00
-- url     : https://prove2.me/submissions/525e1564-67a2-4830-8dc1-d2aa82e0c582

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_exists_depthCut
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_getElem_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_upperOcc
public import Theorems.Thm_DeciSigma1_Holes_Fresh_ne_nil_of_mem_upperOccurrences
public import Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_spec
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
theorem _root_.solution (t : ℕ) :
    upperTexts W t ⊆ (upperParses W (t + 1)).biUnion List.toFinset := by
  intro z hz
  obtain ⟨o, ho, rfl⟩ := mem_image.mp hz
  have hospec := upperOcc_spec ho
  let A := (anchors W (t + 2) o.1).filter fun q => o.2.2 ≤ q
  have hA : A.Nonempty := ⟨(W o.1).length, mem_filter.mpr
    ⟨mem_insert_self _ _, hospec.2.1⟩⟩
  let e := A.min' hA
  have heA : e ∈ A := min'_mem A hA
  have he := (mem_filter.mp heA).1
  have hqe := (mem_filter.mp heA).2
  let o' := (o.1, upperOccurrenceStart W (t + 1) o.1 e, e)
  have ho' : o' ∈ upperOccurrences W (t + 1) := mem_upperOcc.mpr
    ⟨ne_nil_of_mem_upperOccurrences (o := o) ho, he, rfl⟩
  have hs : o'.2.1 < o.2.2 := by
    by_cases hex : ∃ q ∈ anchors W (t + 2) o.1, q < e
    · have hpr := previousAnchor_spec hex
      by_contra hbad
      have hprA : previousAnchor (anchors W (t + 2) o.1) e ∈ A := mem_filter.mpr ⟨hpr.1, by
        change ¬ previousAnchor (anchors W (t + 2) o.1) e < o.2.2 at hbad
        omega⟩
      have hmin := min'_le A _ hprA
      change e ≤ _ at hmin
      omega
    · have hzero : upperOccurrenceStart W (t + 1) o.1 e ≤ 0 := previousAnchor_le (fun q hq hqe =>
        False.elim (hex ⟨q, hq, hqe⟩))
      change upperOccurrenceStart W (t + 1) o.1 e < o.2.2
      omega
  have hq := (mem_upperOcc.mp ho).2.1
  obtain ⟨d, hd, hcut⟩ := exists_depthCut ho' hq hs hqe
  have hdl : d < (reversedBlocks W (t + 1) o').length := by simpa using hd
  have hstart : depthCut W (t + 1) o' (d + 1) = o.2.1 := by
    change previousAnchor (anchors W (t + 1) o.1) (depthCut W (t + 1) o' d) = _
    rw [hcut, (mem_upperOcc.mp ho).2.2]
    rfl
  have htext : (reversedBlocks W (t + 1) o')[d] = occurrenceText W o := by
    rw [getElem_reversedBlocks, hcut, hstart]
    rfl
  apply mem_biUnion.mpr
  refine ⟨upperParse W (t + 1) o', mem_image_of_mem _ ho', ?_⟩
  rw [List.mem_toFinset, upperParse, List.mem_reverse, ← htext]
  exact List.getElem_mem hdl
end DeciSigma1.Holes.Fresh
