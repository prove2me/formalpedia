-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.card_le_of_subset_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:41.669508+00:00
-- url     : https://prove2.me/submissions/7bd0d500-7cb4-4846-bf21-a5005f71fa1f

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
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_suffixOccurrenceCuts_le
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
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
theorem _root_.solution {T : Table α S k} {W : Fin k → List α}
    (hfr : ∀ i, T.Fresh W i) (z : List α) (f : Fin k → ℕ → ℕ) {P : Finset ℕ}
    (hP : P ⊆ univ.biUnion (fun j => (suffixOccurrenceCuts W j z).image (f j))) :
    P.card ≤ k * (Fintype.card S - 1) := by
  calc P.card ≤ (univ.biUnion (fun j => (suffixOccurrenceCuts W j z).image (f j))).card :=
      card_le_card hP
    _ ≤ ∑ j, ((suffixOccurrenceCuts W j z).image (f j)).card := card_biUnion_le
    _ ≤ ∑ _j : Fin k, (Fintype.card S - 1) :=
        sum_le_sum (fun j _ => card_image_le.trans (card_suffixOccurrenceCuts_le hfr j z))
    _ = k * (Fintype.card S - 1) := by simp
end DeciSigma1.Holes.Fresh
