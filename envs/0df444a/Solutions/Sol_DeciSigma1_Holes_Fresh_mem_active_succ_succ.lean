-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.mem_active_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:27.551124+00:00
-- url     : https://prove2.me/submissions/005acdeb-2a13-4e4e-b0d7-240f94e9f0da

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_active
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_level_succ_succ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_succ
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
variable (W : Fin k → List α)
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {t : ℕ} {l : Fin k} :
    l ∈ active W (t + 2) ↔
      l ∈ active W (t + 1) ∧ ∃ e ∈ anchors W (t + 1) l, e < (W l).length := by
  simp only [active, level_succ_succ, Level.next_active, anchors, mem_insert, contextAnchors_succ]
  constructor
  · rintro ⟨h1, e, he, hlt⟩; exact ⟨h1, e, Or.inr he, hlt⟩
  · rintro ⟨h1, e, he | he, hlt⟩
    · omega
    · exact ⟨h1, e, he, hlt⟩
end DeciSigma1.Holes.Fresh
