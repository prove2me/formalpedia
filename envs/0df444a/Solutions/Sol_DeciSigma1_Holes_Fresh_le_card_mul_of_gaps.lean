-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.le_card_mul_of_gaps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:37:56.307942+00:00
-- url     : https://prove2.me/submissions/4786340e-4d9e-47e8-9984-95b4b0a75171

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
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
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (A : Finset ℕ) (E : ℕ) (h0 : 0 ∈ A) (hgap : ∀ a ∈ A, ∀ b ∈ A, a < b →
      (∀ c ∈ A, ¬ (a < c ∧ c < b)) → b - a ≤ E) :
    ∀ x ∈ A, x ≤ A.card * E := by
  induction A using Finset.induction_on_max with
  | empty => simp at h0
  | insert a A hmax ih =>
    have ha : a ∉ A := fun h => (hmax a h).false
    rw [card_insert_of_notMem ha]
    by_cases hem : A = ∅
    · subst A
      simp only [mem_insert, notMem_empty, or_false] at h0
      subst a
      simp
    · have hne := nonempty_iff_ne_empty.mpr hem
      have h0A : 0 ∈ A := by
        rcases mem_insert.mp h0 with h | h
        · obtain ⟨x, hx⟩ := hne
          have := hmax x hx
          omega
        · exact h
      have hi := ih h0A (fun b hb c hc hbc hno =>
        hgap b (mem_insert_of_mem hb) c (mem_insert_of_mem hc) hbc (by
          intro d hd hbd
          rcases mem_insert.mp hd with rfl | hd
          · have := hmax c hc; omega
          · exact hno d hd hbd))
      have hmem := max'_mem A hne
      have htop := hmax _ hmem
      have hlast : a - A.max' hne ≤ E :=
          hgap _ (mem_insert_of_mem hmem) a (mem_insert_self _ _) htop (by
        intro c hc hbetween
        rcases mem_insert.mp hc with rfl | hc
        · omega
        · have := le_max' A c hc; omega)
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · have := hi _ hmem
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · exact (hi x hx).trans (Nat.mul_le_mul_right _ (by omega))
end DeciSigma1.Holes.Fresh
