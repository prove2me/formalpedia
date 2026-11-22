-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.anchors_eq_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:30:52.047441+00:00
-- url     : https://prove2.me/submissions/688e1e53-5ea8-43f2-946d-284a69e98304

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_mem_markerEndCuts
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_active
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_succ_succ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchors_succ_subset
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
variable {W : Fin k → List α}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {t : ℕ} (ht : 1 ≤ t) {l : Fin k}
    (hl : l ∉ active W (t + 1)) : anchors W t l = {(W l).length} := by
  induction t with
  | zero => omega
  | succ t ih =>
    apply le_antisymm _ (singleton_subset_iff.mpr (mem_insert_self _ _))
    by_cases hl' : l ∈ active W (t + 1)
    · intro e he
      rw [mem_singleton]
      by_contra hne'
      have hle : e ≤ (W l).length := by
        rcases mem_insert.mp he with rfl | he
        · exact le_rfl
        · rcases t with _ | t
          · exact (Level.mem_markerEndCuts.mp he).1
          · exact (Level.mem_markerEndCuts.mp he).1
      rcases t with _ | t
      · exact hl (Level.next_active.mpr ⟨hl', e, (mem_insert.mp he).resolve_left hne', by omega⟩)
      · exact hl ((mem_active_succ_succ W).mpr ⟨hl', e, he, by omega⟩)
    · rcases t with _ | t
      · intro e he
        have hnil : W l = [] := not_not.mp (fun h => hl' ((mem_active_one W).mpr h))
        rcases mem_insert.mp he with rfl | he
        · exact mem_singleton_self _
        · have := (Level.mem_markerEndCuts.mp he).1
          rw [hnil] at this ⊢
          exact mem_singleton.mpr (by simpa using this)
      · rw [← ih (by omega) hl']
        exact anchors_succ_subset _ l
end DeciSigma1.Holes.Fresh
