-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.flatten_upperParse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:37:31.30893+00:00
-- url     : https://prove2.me/submissions/33d23660-8f40-4337-bac6-5b297e4b8e4f

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_take_depthCut_append
public import Theorems.Thm_DeciSigma1_Holes_Fresh_take_start_append_occurrenceText
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks



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
    (upperParse W t o).flatten = occurrenceText W o := by
  have h := take_depthCut_append ho (d := lowerBlockCount W t o) le_rfl
  rw [(depthCut_spec ho).2, ← length_reversedBlocks W t o, List.take_length] at h
  apply List.append_cancel_left (as := (W o.1).take o.2.1)
  exact h.trans (take_start_append_occurrenceText ho).symm
end DeciSigma1.Holes.Fresh
