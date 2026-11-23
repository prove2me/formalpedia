-- Prove2me | solution 1 for Bdd.ordered_of_low_high_ordered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:59:20.343238+00:00
-- url     : https://prove2.me/submissions/9ea2f0ef-a50a-4e5e-b8b1-04918d82b50c

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_Bdd_low_root_eq_low
import Theorems.Thm_Bdd_high_root_eq_high
import Theorems.Thm_OBdd_low_root_eq_low
import Theorems.Thm_OBdd_high_root_eq_high
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace Bdd
theorem _root_.solution {B : Bdd n m} (h : B.root = node j):
    (B.low h).Ordered → B.var < (B.low h).var → (B.high h).Ordered → B.var < (B.high h).var → Ordered B := by
  rintro hl1 hl2 hh1 hh2 ⟨x, hx⟩ ⟨y, hy⟩ hxy
  simp only [RelevantEdge] at hxy
  simp only [RelevantMayPrecede, MayPrecede, Nat.succ_eq_add_one]
  cases Relation.reflTransGen_swap.mp hx
  case refl        =>
    rw [h] at hxy
    rw [h]
    cases hxy with
    | low heq =>
      simp only [var, low_heap_eq_heap, low_root_eq_low, heq, h] at hl2
      exact hl2
    | high heq =>
      simp only [var, high_heap_eq_heap, high_root_eq_high, heq, h] at hh2
      exact hh2
  case tail p r e =>
    rw [h] at e
    cases e with
    | low heq =>
      rw [← low_heap_eq_heap (h := h)]
      rw [← low_heap_eq_heap (h := h)] at hxy
      rw [← low_heap_eq_heap (h := h)] at r
      rw [← heq] at r
      have := @hl1 ⟨x, Relation.reflTransGen_swap.mpr r⟩ ⟨y, by trans x; exact Relation.reflTransGen_swap.mpr r; right; left; exact hxy⟩ hxy
      exact this
    | high heq =>
      rw [← high_heap_eq_heap (h := h)]
      rw [← high_heap_eq_heap (h := h)] at hxy
      rw [← high_heap_eq_heap (h := h)] at r
      rw [← heq] at r
      have := @hh1 ⟨x, Relation.reflTransGen_swap.mpr r⟩ ⟨y, by trans x; exact Relation.reflTransGen_swap.mpr r; right; left; exact hxy⟩ hxy
      exact this
end Bdd
