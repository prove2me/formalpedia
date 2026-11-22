-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.take_of_suffix_take
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:35:20.973798+00:00
-- url     : https://prove2.me/submissions/d473b6ec-1862-4729-a0af-aff4ed8845fa

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
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
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
omit [DecidableEq α] [Fintype S]
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution {x τ : List α} {c : ℕ} (hc : c ≤ x.length) (hs : τ <:+ x.take c)
    {e : ℕ} (he : e ≤ τ.length) :
    x.take (c - e) = x.take (c - τ.length) ++ τ.take (τ.length - e) ∧
      (x.drop (c - e)).take e = τ.drop (τ.length - e) := by
  obtain ⟨s', hs'⟩ := hs
  have hτc : τ.length ≤ c := by
    have := congrArg List.length hs'; simp at this; omega
  have hs'l : s'.length = c - τ.length := by
    have := congrArg List.length hs'; simp at this; omega
  have hpre : x.take (c - τ.length) = s' := by
    rw [show x.take (c - τ.length) = (x.take c).take (c - τ.length) by
      rw [List.take_take, Nat.min_eq_left (by omega)], ← hs', List.take_left' hs'l]
  have hcat : x.take c = x.take (c - τ.length) ++ τ := by rw [hpre, hs']
  have hl1 : (x.take (c - τ.length)).length = c - τ.length := by simp; omega
  constructor
  · rw [show x.take (c - e) = (x.take c).take (c - e) by
      rw [List.take_take, Nat.min_eq_left (by omega)], hcat, List.take_append,
      List.take_of_length_le (by omega), hl1]
    congr 2; omega
  · rw [show (x.drop (c - e)).take e = (x.take c).drop (c - e) by
      rw [List.drop_take]; congr 1; omega, hcat, List.drop_append,
      List.drop_of_length_le (by omega), List.nil_append, hl1]
    congr 1; omega
end DeciSigma1.Holes.Fresh.BlockDeletion
