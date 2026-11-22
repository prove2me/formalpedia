-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Edge.lowerLevelTypes_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:36:59.596856+00:00
-- url     : https://prove2.me/submissions/5463951b-ab97-4d5f-b534-603dcaf6855e

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_take_eq_top_append
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_marker_fits
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_edgePrefix_length
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_markerTypes
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
namespace Edge
theorem _root_.solution (hfr : ∀ i, T.Fresh W i)
    {t : ℕ} (e : Edge W t) {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : e.TraversedBy o) {p : ℕ} (hp0 : 0 < p)
    (hp : p + deletionMargin k (Fintype.card S) ≤ e.endDepth) :
    lowerLevelTypes W t (W o.1) (depthCut W t o p) =
      lowerLevelTypes W t (edgePrefix e p) (edgePrefix e p).length := by
  have hp' : p ≤ e.endDepth := by omega
  funext r
  apply Finset.ext
  intro τ
  simp only [lowerLevelTypes, mem_markerTypes, List.take_length]
  constructor
  · rintro ⟨m, hm, hs, rfl⟩
    have hfit := e.marker_fits hfr ho hth hp0 hp (by omega) (by omega : r.val + 1 ≤ t) hm hs
    rw [← e.edgePrefix_length ho hth hp'] at hfit
    rw [e.take_eq_top_append ho hth hp'] at hs
    exact ⟨m, hm, List.suffix_of_suffix_length_le hs (List.suffix_append _ _) hfit, rfl⟩
  · rintro ⟨m, hm, hs, rfl⟩
    refine ⟨m, hm, ?_, rfl⟩
    rw [e.take_eq_top_append ho hth hp']
    exact hs.trans (List.suffix_append _ _)
end Edge
end DeciSigma1.Holes.Fresh
