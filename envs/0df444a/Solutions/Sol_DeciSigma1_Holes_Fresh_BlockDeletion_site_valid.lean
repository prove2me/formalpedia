-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.site_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:28:59.106089+00:00
-- url     : https://prove2.me/submissions/5b8d18a5-b6e8-47e3-9738-14afdb00852b

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_types_iff_of_lowerLevelTypes
public import Theorems.Thm_DeciSigma1_Holes_Fresh_runPrefix_eq_of_label
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_mem_sites
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_succ
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
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution {l : Fin k} {c : ℕ} (hc : c ∈ m.sites l) :
    ValidDeletionSite W t (W l) c m.deletionLength ∧ c + m.deletionLength < (W l).length ∧
      runFrom T.step (T.start l) ((W l).take c) =
          runFrom T.step (T.start l) ((W l).take (c + m.deletionLength)) := by
  obtain ⟨o, ho, rfl, hth, rfl⟩ := m.mem_sites.mp hc
  obtain ⟨hsj, hji, hie, hE, hd, hjA, hiA⟩ := m.site_spec ho hth
  rw [hd]
  have hlab := m.labels_eq o ho hth
  have hnotup := (upperOcc_spec ho).2.2.2.2
  refine ⟨⟨by omega, ?_, ?_, ?_⟩, by omega, ?_⟩
  · intro ht
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have hmem : depthCut W (t' + 1) o m.maxDepth ∈ contextAnchors W (t' + 1) (W o.1) := by
      rcases mem_insert.mp hjA with h | h
      · omega
      · exact h
    obtain ⟨-, m0, hm0, hs⟩ := (mem_contextAnchors_succ W).mp hmem
    exact ⟨m0, hm0, hs⟩
  · intro r hr1 hr mm hmm
    simp only [label, Prod.mk.injEq] at hlab
    rw [hd]
    exact types_iff_of_lowerLevelTypes hlab.1 hr1 hr hmm
  · intro mm hmm hs
    rw [hd] at hs
    have hmem : depthCut W t o m.minDepth ∈ anchors W (t + 1) o.1 :=
      mem_insert_of_mem ((mem_contextAnchors_succ W).mpr ⟨by omega, mm, hmm, hs⟩)
    exact hnotup _ hmem ⟨by omega, hie⟩
  · exact runPrefix_eq_of_label T (by omega) (by omega) hlab
end DeciSigma1.Holes.Fresh.BlockDeletion
