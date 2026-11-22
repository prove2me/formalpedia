-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Edge.take_eq_top_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:59:45.538043+00:00
-- url     : https://prove2.me/submissions/c99ed541-f5e1-4194-822b-f0f90eb72553

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_take_depthCut_append
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_depthCut_through
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_through_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_lt_of_lt
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
namespace DeciSigma1.Holes.Fresh
namespace Edge
theorem _root_.solution {t : ℕ} (e : Edge W t)
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) (hth : e.TraversedBy o)
    {p : ℕ} (hp : p ≤ e.endDepth) :
    (W o.1).take (depthCut W t o p) =
      (W o.1).take (depthCut W t o e.endDepth) ++ edgePrefix e p := by
  have hb := (e.through_iff.mp hth).1
  have hcut := e.depthCut_through ho hth hp
  have htop := e.depthCut_through ho hth le_rfl
  have hbound := (upperOcc_spec ho).2.1
  have hpre : depthCut W t o e.endDepth ≤ depthCut W t o p := by
    rcases lt_or_eq_of_le hp with h | rfl
    · exact (depthCut_lt_of_lt ho h hb).le
    · exact le_rfl
  have htext := take_depthCut_append ho hb
  rw [(e.through_iff.mp hth).2] at htext
  have ht := congrArg (List.take (depthCut W t o p)) htext
  rw [List.take_take, Nat.min_eq_left (by omega)] at ht
  rw [List.take_append, List.take_take, Nat.min_eq_right hpre] at ht
  simpa only
      [List.length_take, Nat.min_eq_left (by omega : depthCut W t o e.endDepth ≤ (W o.1).length),
    show depthCut W t o p - depthCut W t o e.endDepth =
      firstBlocksLength e.blocks.reverse e.endDepth - firstBlocksLength e.blocks.reverse p by omega,
    edgePrefix, edgeText] using ht.symm
end Edge
end DeciSigma1.Holes.Fresh
