-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.card_prefixOccurrenceCuts_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:24:31.774904+00:00
-- url     : https://prove2.me/submissions/c8a8ec32-9fc8-4301-87c9-825a114109a5

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_suffixOccurrenceCuts
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_le_of_subset_biUnion
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
open DeciSigma1.Readers.Table
variable {S : Type} [Fintype S] [DecidableEq S]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {T : Table α S k} {W : Fin k → List α} (hfr : ∀ i, T.Fresh W i)
    (z : List α) : (prefixOccurrenceCuts W z).card ≤ k * (Fintype.card S - 1) := by
  refine card_le_of_subset_biUnion hfr z (fun j b => (W j).length - b) ?_
  intro p hp
  simp only [prefixOccurrenceCuts, mem_filter, mem_Icc] at hp
  obtain ⟨⟨hp1, hp2⟩, j, hj⟩ := hp
  have hlen : (z.take p).length = p := by simp; omega
  have hpj : p ≤ (W j).length := hlen ▸ hj.length_le
  have hdrop : (W j).drop ((W j).length - p) = z.take p := by
    rw [List.suffix_iff_eq_drop.mp hj, hlen]
  simp only [mem_biUnion, mem_univ, true_and, mem_image]
  refine ⟨j, (W j).length - p, mem_suffixOccurrenceCuts.mpr ⟨by omega, ?_⟩, by omega⟩
  rw [hdrop]; exact List.take_prefix _ _
end DeciSigma1.Holes.Fresh
