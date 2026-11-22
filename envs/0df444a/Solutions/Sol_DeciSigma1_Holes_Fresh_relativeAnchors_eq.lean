-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.relativeAnchors_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:31:06.455133+00:00
-- url     : https://prove2.me/submissions/9adafa7f-7ed7-4c66-91b2-b66f248e808a

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_append_right
public import Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_of_append_right
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_ne_nil
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_succ
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks
attribute [local simp] DeciSigma1.Holes.Fresh.length_upperSeq

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {t : ℕ} (ht : 1 ≤ t) (u z : List α) :
    relativeAnchors W t u z = contextAnchors W t z ∪ crossBoundaryMarkerEnds W t u z := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  ext p
  simp only [relativeAnchors, crossBoundaryMarkerEnds, mem_union, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hp1, hp2⟩, hp⟩
    obtain ⟨-, m, hm, hs⟩ := (mem_contextAnchors_succ W).mp hp
    by_cases hin : (marker W (t + 1) m).length ≤ p
    · exact Or.inl (contextAnchors_of_append_right ht hm hs hp2 hin)
    · exact Or.inr ⟨⟨hp1, hp2⟩, m, hm, hs, by omega⟩
  · rintro (hp | ⟨⟨hp1, hp2⟩, m, hm, hs, -⟩)
    · obtain ⟨hle, m, hm, hs⟩ := (mem_contextAnchors_succ W).mp hp
      have h1 := List.length_pos_iff.mpr (marker_ne_nil ht hm)
      have h2 := hs.length_le
      simp only [List.length_take] at h2
      exact ⟨⟨by omega, hle⟩, contextAnchors_append_right hp⟩
    · refine ⟨⟨hp1, hp2⟩, (mem_contextAnchors_succ W).mpr ⟨by simp; omega, m, hm, hs⟩⟩
end DeciSigma1.Holes.Fresh
