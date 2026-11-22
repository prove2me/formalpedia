-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.windowLength_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:59:07.556089+00:00
-- url     : https://prove2.me/submissions/3740eaf0-9a34-454b-b575-6883b3a9f10f

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_markerTypes
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
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution {u : List α} {c : ℕ} (hw : 0 < windowLength W t u c) :
    ∃ r, 1 ≤ r ∧ r ≤ t ∧ ∃ g ∈ active W r, marker W r g <:+ u.take c ∧
      (marker W r g).length = windowLength W t u c := by
  have hne1 : (univ : Finset (Fin t)).Nonempty := by
    by_contra hem
    rw [not_nonempty_iff_eq_empty] at hem
    simp [windowLength, hem] at hw
  obtain ⟨r, -, hr⟩ := exists_mem_eq_sup _ hne1
    (fun r : Fin t => (lowerLevelTypes W t u c r).sup List.length)
  have hne2 : (lowerLevelTypes W t u c r).Nonempty := by
    by_contra hem
    rw [not_nonempty_iff_eq_empty] at hem
    have : windowLength W t u c = 0 := by rw [windowLength, hr, hem, sup_empty]; rfl
    omega
  obtain ⟨τ, hτ, hτl⟩ := exists_mem_eq_sup _ hne2 List.length
  obtain ⟨g, hg, hs, rfl⟩ := mem_markerTypes.mp hτ
  exact ⟨r.1 + 1, by omega, by omega, g, hg, hs, by rw [windowLength, hr, hτl]⟩
end DeciSigma1.Holes.Fresh.BlockDeletion
