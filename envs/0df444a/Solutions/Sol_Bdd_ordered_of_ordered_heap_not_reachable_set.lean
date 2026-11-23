-- Prove2me | solution 1 for Bdd.ordered_of_ordered_heap_not_reachable_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:10:35.054939+00:00
-- url     : https://prove2.me/submissions/e152725c-8b47-4fb7-b69c-2dd1834dae44

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_P2M_Pointer_toVar_heap_set__d9257dfabaf5
import Theorems.Thm_Bdd_low_root_eq_low
import Theorems.Thm_Bdd_high_root_eq_high
import Theorems.Thm_OBdd_low_root_eq_low
import Theorems.Thm_OBdd_high_root_eq_high
import Theorems.Thm_Bdd_ordered_of_low_high_ordered
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace Bdd
theorem _root_.solution (O : OBdd n m) :
    ∀ i N, ¬ Reachable O.1.heap O.1.root (node i) → Ordered ⟨O.1.heap.set i N, O.1.root⟩ := by
  intro i N unr
  cases O_root_def : O.1.root with
  | terminal b => exact Ordered_of_terminal
  | node j =>
    have : i ≠ j := by
      intro contra
      rw [contra] at unr
      rw [O_root_def] at unr
      apply unr
      left
    apply ordered_of_low_high_ordered rfl
    · simp only [low, Fin.getElem_fin]
      simp only [Vector.getElem_set_ne i.2 j.2 (by simp_all [Fin.val_ne_of_ne this])]
      have that := solution (O.low O_root_def) i N
      simp only [OBdd.low_heap_eq_heap] at that
      simp only [OBdd.low_root_eq_low] at that
      apply that
      intro contra
      apply unr
      trans O.1.heap[j].low
      · right
        left
        rw [O_root_def]
        left
        rfl
      · exact contra
    · simp only [Nat.succ_eq_add_one, var, low]
      simp only [Fin.getElem_fin]
      simp only [Vector.getElem_set_ne i.2 j.2 (by simp_all [Fin.val_ne_of_ne this])]
      rw [toVar_heap_set' this]
      have that : toVar O.1.heap (node j) < toVar O.1.heap O.1.heap[j].low := by
        exact @O.2 ⟨node j, (by rw [O_root_def]; left)⟩
                   ⟨O.1.heap[j].low, (by trans (node j); rw [O_root_def]; left; right; left; left; rfl)⟩
                   (by left; rfl)
      convert that using 1
      cases low_def : O.1.heap[j].low with
      | terminal bl => simp
      | node jl =>
        simp only [toVar]
        simp only [Nat.succ_eq_add_one, Ordered]
        simp only [Fin.getElem_fin]
        simp only [Fin.mk.injEq]
        rw [Vector.getElem_set_ne i.2 jl.2]
        intro contra
        rcases i with ⟨iv, ih⟩
        simp at contra
        simp_rw [contra] at unr
        apply unr
        trans (node j)
        · rw [O_root_def]; left
        · rw [← low_def]; right; left; left; rfl
    · simp only [high, Fin.getElem_fin]
      simp only [Vector.getElem_set_ne i.2 j.2 (by simp_all [Fin.val_ne_of_ne this])]
      have that := solution (O := (O.high O_root_def)) i N
      simp only [OBdd.high_heap_eq_heap] at that
      simp only [OBdd.high_root_eq_high] at that
      apply that
      intro contra
      apply unr
      trans O.1.heap[j].high
      · right
        left
        rw [O_root_def]
        right
        rfl
      · exact contra
    · simp only [Nat.succ_eq_add_one, var, high]
      simp only [Fin.getElem_fin]
      simp only [Vector.getElem_set_ne i.2 j.2 (by simp_all [Fin.val_ne_of_ne this])]
      rw [toVar_heap_set' this]
      have that : toVar O.1.heap (node j) < toVar O.1.heap O.1.heap[j].high := by
        exact @O.2 ⟨node j, (by rw [O_root_def]; left)⟩
                   ⟨O.1.heap[j].high, (by trans (node j); rw [O_root_def]; left; right; left; right; rfl)⟩
                   (by right; rfl)
      convert that using 1
      cases high_def : O.1.heap[j].high with
      | terminal bh => simp
      | node bh =>
        simp only [toVar]
        simp only [Nat.succ_eq_add_one, Ordered]
        simp only [Fin.getElem_fin]
        simp only [Fin.mk.injEq]
        rw [Vector.getElem_set_ne i.2 bh.2]
        intro contra
        rcases i with ⟨iv, ih⟩
        simp at contra
        simp_rw [contra] at unr
        apply unr
        trans (node j)
        · rw [O_root_def]; left
        · rw [← high_def]; right; left; right; rfl
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
end Bdd
