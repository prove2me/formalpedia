-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.label_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:35:57.890438+00:00
-- url     : https://prove2.me/submissions/b292a1df-3419-41e8-8e3d-bc154f035072

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_windowLength_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_take_of_suffix_take
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_markerTypes
public import Theorems.Thm_DeciSigma1_Holes_Fresh_runPrefix_eq_of_label
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
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
omit [Fintype S]
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution {l : Fin k} {c c' : ℕ} (hc : c ≤ (W l).length) (hc' : c' ≤ (W l).length)
    (h : label T W t l c = label T W t l c') {e : ℕ} (he : e ≤ windowLength W t (W l) c) :
    e ≤ c ∧ e ≤ c' ∧ ((W l).drop (c - e)).take e = ((W l).drop (c' - e)).take e ∧
      T.runPrefix W l (c - e) = T.runPrefix W l (c' - e) := by
  have h' := h
  simp only [label, Prod.mk.injEq] at h'
  obtain ⟨hL, hq⟩ := h'
  have hw : windowLength W t (W l) c = windowLength W t (W l) c' := by simp only [windowLength, hL]
  rw [← hw] at hq
  rcases Nat.eq_zero_or_pos (windowLength W t (W l) c) with hw0 | hwpos
  · have he0 : e = 0 := by omega
    subst he0
    exact ⟨Nat.zero_le _, Nat.zero_le _, by simp, by simpa using runPrefix_eq_of_label T hc hc' h⟩
  obtain ⟨r, hr1, hrt, g, hg, hs, hlen⟩ := windowLength_spec hwpos
  have hmem : marker W r g ∈ lowerLevelTypes W t (W l) c' ⟨r - 1, by omega⟩ := by
    rw [← hL]
    simp only [lowerLevelTypes, Nat.sub_add_cancel hr1]
    exact mem_markerTypes.mpr ⟨g, hg, hs, rfl⟩
  simp only [lowerLevelTypes, Nat.sub_add_cancel hr1] at hmem
  obtain ⟨g', -, hs', he'⟩ := mem_markerTypes.mp hmem
  rw [he'] at hs'
  have hcl := hs.length_le
  have hcl' := hs'.length_le
  simp only [List.length_take] at hcl hcl'
  obtain ⟨t1, d1⟩ := take_of_suffix_take hc hs (e := e) (by omega)
  obtain ⟨t2, d2⟩ := take_of_suffix_take hc' hs' (e := e) (by omega)
  refine ⟨by omega, by omega, by rw [d1, d2], ?_⟩
  simp only [Table.runPrefix]
  rw [t1, t2, runFrom_append, runFrom_append]
  simp only [Table.runPrefix] at hq
  rw [hlen, hq]
end DeciSigma1.Holes.Fresh.BlockDeletion
