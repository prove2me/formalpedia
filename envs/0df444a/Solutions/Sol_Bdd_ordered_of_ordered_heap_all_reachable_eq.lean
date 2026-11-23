-- Prove2me | solution 1 for Bdd.ordered_of_ordered_heap_all_reachable_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:05:43.539926+00:00
-- url     : https://prove2.me/submissions/c52e7ce7-9fc3-4f70-97cd-4199012df642

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_P2M_Bdd_Ordered_of_terminal__2f4d39cf78e1
import Theorems.Thm_OBdd_var_lt_high_var
import Theorems.Thm_OBdd_var_lt_low_var
import Theorems.Thm_Bdd_ordered_of_low_high_ordered
import Theorems.Thm_Pointer_equiv_symm
import Theorems.Thm_Node_equiv_symm
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace Bdd
theorem _root_.solution (O : OBdd n m) (B : Bdd n m') :
    (∀ j : Fin m', Reachable B.heap B.root (node j) → ∃ hj : j.1 < m, Node.equiv O.1.heap[j.1] B.heap[j]) →
    (∀ j, B.root = .node j → ∃ hj, O.1.root = .node ⟨j.1, hj⟩) →
    Ordered B := by
  intro h1 h2
  cases B_root_def : B.root with
  | terminal b => exact Ordered_of_terminal' B_root_def
  | node j =>
    rcases h2 _ B_root_def with ⟨hj1', hj2'⟩
    apply ordered_of_low_high_ordered B_root_def
    · apply solution (O.low hj2')
      · intro jj hrjj
        simp only [low_heap_eq_heap]
        apply h1
        apply Relation.reflTransGen_swap.mpr
        right
        exact Relation.reflTransGen_swap.mp hrjj
        exact edge_of_low B
      · intro jl B_low_def
        simp only [OBdd.low, Bdd.low, Fin.getElem_fin]
        rcases h1 jl (.tail .refl (by rw [← B_low_def]; exact edge_of_low _)) with ⟨hjl1, _⟩
        rcases h1 j (by rw [← B_root_def]; left) with ⟨hj1, hj2, hj3, hj4⟩
        rcases Pointer.equiv_symm hj3 with ⟨hj31, hj32⟩
        use hjl1
        simp only [Bdd.low] at B_low_def
        rcases hj32 _ B_low_def with ⟨j', hj1', hj2'⟩
        rw [hj1']
        simp only [node.injEq]
        exact Fin.eq_mk_iff_val_eq.mpr (id (Eq.symm hj2'))
    · rcases h1 j (by rw [← B_root_def]; left) with ⟨hj1, hj2, hj3, hj4⟩
      have := OBdd.var_lt_low_var (O := O) (h := hj2')
      simp_all [OBdd.var, Bdd.var, OBdd.low, Bdd.low]
      apply Fin.lt_def.mpr
      simp only [toVar]
      have that : (toVar B.heap B.heap[j.1].low).1 = (toVar O.1.heap O.1.heap[j.1].low).1 := by
        rcases Pointer.equiv_symm hj3 with ⟨hj31, hj32⟩
        cases hl : B.heap[↑j].low with
        | terminal b =>
          simp [hj31 b hl]
        | node jl =>
          rcases hj32 jl hl with ⟨jl', hjl1', hjl2'⟩
          rw [hjl1']
          simp only [Nat.succ_eq_add_one, toVar_node_eq, Fin.getElem_fin]
          simp_rw [← hjl2']
          rcases h1 jl (by rw [← hl]; exact reachable_of_edge (.low rfl)) with ⟨hs1, hs2, _, _⟩
          exact symm hs2
      simp only [toVar] at that
      rw [that]
      exact this
    · apply solution (O.high hj2')
      · intro jj hrjj
        simp only [high_heap_eq_heap]
        apply h1
        apply Relation.reflTransGen_swap.mpr
        right
        exact Relation.reflTransGen_swap.mp hrjj
        exact edge_of_high B
      · intro jl B_high_def
        simp only [OBdd.high, Bdd.high, Fin.getElem_fin]
        rcases h1 jl (.tail .refl (by rw [← B_high_def]; exact edge_of_high _)) with ⟨hjl1, _⟩
        rcases h1 j (by rw [← B_root_def]; left) with ⟨hj1, hj2, hj3, hj4⟩
        rcases Pointer.equiv_symm hj4 with ⟨hj41, hj42⟩
        use hjl1
        simp only [Bdd.high] at B_high_def
        rcases hj42 _ B_high_def with ⟨j', hj1', hj2'⟩
        rw [hj1']
        simp only [node.injEq]
        exact Fin.eq_mk_iff_val_eq.mpr (id (Eq.symm hj2'))
    · rcases h1 j (by rw [← B_root_def]; left) with ⟨hj1, hj2, hj3, hj4⟩
      have := OBdd.var_lt_high_var (O := O) (h := hj2')
      simp_all [OBdd.var, Bdd.var, OBdd.high, Bdd.high]
      apply Fin.lt_def.mpr
      simp only [toVar]
      have that : (toVar B.heap B.heap[j.1].high).1 = (toVar O.1.heap O.1.heap[j.1].high).1 := by
        rcases Pointer.equiv_symm hj4 with ⟨hj41, hj42⟩
        cases hl : B.heap[↑j].high with
        | terminal b =>
          simp [hj41 b hl]
        | node jl =>
          rcases hj42 jl hl with ⟨jl', hjl1', hjl2'⟩
          rw [hjl1']
          simp only [Nat.succ_eq_add_one, toVar_node_eq, Fin.getElem_fin]
          simp_rw [← hjl2']
          rcases h1 jl (by rw [← hl]; exact reachable_of_edge (.high rfl)) with ⟨hs1, hs2, _, _⟩
          exact symm hs2
      simp only [toVar] at that
      rw [that]
      exact this
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
end Bdd
