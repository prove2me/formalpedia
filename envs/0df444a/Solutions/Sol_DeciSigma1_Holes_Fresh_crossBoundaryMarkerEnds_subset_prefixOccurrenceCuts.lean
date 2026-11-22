-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.crossBoundaryMarkerEnds_subset_prefixOccurrenceCuts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:42.094905+00:00
-- url     : https://prove2.me/submissions/1081104c-3541-4953-a3f8-a404e43992ae

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_suffix
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
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
theorem _root_.solution {t : ℕ} (u z : List α) :
    crossBoundaryMarkerEnds W t u z ⊆ prefixOccurrenceCuts W z := by
  intro p hp
  simp only [crossBoundaryMarkerEnds, mem_filter, mem_Icc] at hp
  obtain ⟨⟨hp1, hp2⟩, m, -, hs, hlt⟩ := hp
  rw [List.take_length_add_append] at hs
  have hout : z.take p <:+ marker W t m :=
    List.suffix_of_suffix_length_le (List.suffix_append _ _) hs (by simp; omega)
  simp only [prefixOccurrenceCuts, mem_filter, mem_Icc]
  exact ⟨⟨hp1, hp2⟩, m, hout.trans (marker_suffix W t m)⟩
end DeciSigma1.Holes.Fresh
