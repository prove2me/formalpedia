-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.label_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:37:45.319611+00:00
-- url     : https://prove2.me/submissions/f5584536-9220-45a0-b7e1-3734302fdfdd

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_take_eq_top_append
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_bounds
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_edgePrefix_length
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_lowerLevelTypes_local
public import Theorems.Thm_DeciSigma1_Holes_Fresh_windowLength_le
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_through_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_lt_of_lt
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperOcc_spec
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_append
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
theorem _root_.solution (hfr : ∀ i, T.Fresh W i)
    {t : ℕ} (e : Edge W t) {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : e.TraversedBy o) {p : ℕ} (hp0 : 0 < p)
    (hp : p + deletionMargin k (Fintype.card S) ≤ e.endDepth) :
    label T W t o.1 (depthCut W t o p) =
      (lowerLevelTypes W t (edgePrefix e p) (edgePrefix e p).length,
        edgeMap T e p (T.runPrefix W o.1 (depthCut W t o e.endDepth))) := by
  have hL := e.lowerLevelTypes_local hfr ho hth hp0 hp
  have hw : windowLength W t (W o.1) (depthCut W t o p) =
      windowLength W t (edgePrefix e p) (edgePrefix e p).length := by
    simp only [windowLength, hL]
  have hwl := windowLength_le W t (edgePrefix e p) (edgePrefix e p).length
  have hp' : p ≤ e.endDepth := by omega
  have hb := (e.through_iff.mp hth).1
  have h1 := (depthCut_bounds ho (hp'.trans hb)).2
  have h2 := (depthCut_bounds ho hb).2
  have h3 := (upperOcc_spec ho).2.1
  have hlen := e.edgePrefix_length ho hth hp'
  have hle : depthCut W t o e.endDepth ≤ depthCut W t o p := by
    rcases lt_or_eq_of_le hp' with h | rfl
    · exact (depthCut_lt_of_lt ho h hb).le
    · exact le_rfl
  have htext := congrArg
    (List.take (depthCut W t o p - windowLength W t (edgePrefix e p) (edgePrefix e p).length))
    (e.take_eq_top_append ho hth hp')
  simp only [List.take_take, Nat.min_eq_left (Nat.sub_le _ _)] at htext
  rw [List.take_append, List.take_take, Nat.min_eq_right (by omega)] at htext
  simp only [List.length_take, Nat.min_eq_left (h2.trans h3)] at htext
  rw [show depthCut W t o p - windowLength W t (edgePrefix e p)
      (edgePrefix e p).length - depthCut W t o e.endDepth =
      (edgePrefix e p).length - windowLength W t (edgePrefix e p)
          (edgePrefix e p).length by omega] at htext
  simp only [label, hL, hw, Table.runPrefix, edgeMap]
  rw [htext, runFrom_append]
end DeciSigma1.Holes.Fresh
