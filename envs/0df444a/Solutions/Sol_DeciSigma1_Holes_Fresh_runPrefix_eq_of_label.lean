-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.runPrefix_eq_of_label
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:51:27.256797+00:00
-- url     : https://prove2.me/submissions/8eaa8afc-0a45-421b-a5cf-ef9a8093af96

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_markerTypes
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_take_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_take_occ
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
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {S : Type} [DecidableEq S]
omit [DecidableEq S]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (T : Table α S k) {W : Fin k → List α} {t : ℕ} {l : Fin k}
    {c c' : ℕ} (hc : c ≤ (W l).length) (hc' : c' ≤ (W l).length)
    (h : label T W t l c = label T W t l c') : T.runPrefix W l c = T.runPrefix W l c' := by
  simp only [label, Prod.mk.injEq] at h
  obtain ⟨hL, hq⟩ := h
  have hw : windowLength W t (W l) c = windowLength W t (W l) c' := by simp only [windowLength, hL]
  rw [← hw] at hq
  set w := windowLength W t (W l) c with hwdef
  rcases Nat.eq_zero_or_pos w with hw0 | hwpos
  · rw [hw0] at hq; simpa using hq
  · -- a marker text of length `w` ends at both cuts
    have hne1 : (univ : Finset (Fin t)).Nonempty := by
      by_contra hem
      rw [not_nonempty_iff_eq_empty] at hem
      simp [hwdef, windowLength, hem] at hwpos
    obtain ⟨r, -, hr⟩ :=
        exists_mem_eq_sup _ hne1 (fun r : Fin t => (lowerLevelTypes W t (W l) c r).sup List.length)
    have hne2 : (lowerLevelTypes W t (W l) c r).Nonempty := by
      by_contra hem
      rw [not_nonempty_iff_eq_empty] at hem
      have : w = 0 := by rw [hwdef, windowLength, hr, hem, sup_empty]; rfl
      omega
    obtain ⟨τ, hτ, hτl⟩ := exists_mem_eq_sup _ hne2 List.length
    have hτw : τ.length = w := by rw [hwdef, windowLength, hr, hτl]
    have hτ' : τ ∈ lowerLevelTypes W t (W l) c' r := hL ▸ hτ
    obtain ⟨m1, -, hs1, rfl⟩ := mem_markerTypes.mp hτ
    obtain ⟨m2, -, hs2, he2⟩ := mem_markerTypes.mp hτ'
    rw [he2] at hs2
    obtain ⟨hl1, ho1⟩ := (suffix_take_iff hc).mp hs1
    obtain ⟨hl2, ho2⟩ := (suffix_take_iff hc').mp hs2
    have e1 := take_occ ho1
    have e2 := take_occ ho2
    rw [Nat.sub_add_cancel hl1] at e1
    rw [Nat.sub_add_cancel hl2] at e2
    simp only [Table.runPrefix]
    rw [e1, e2, runFrom_append, runFrom_append, hτw]
    simp only [Table.runPrefix] at hq
    rw [hq]
end DeciSigma1.Holes.Fresh
