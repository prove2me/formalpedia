-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.le_iff_root_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:27.48665+00:00
-- url     : https://prove2.me/submissions/6112158a-7eac-45ad-8799-31494ad8c6d3

module
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Order.Lattice
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Theorems.Thm_DeciSigma1_Semantics_Tree_eq_bot_or_eq_top_or_node
public import Theorems.Thm_DeciSigma1_Semantics_Tree_bot_le
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_top_le_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_node_le_node_iff
attribute [local simp] DeciSigma1.Semantics.Tree.bot_le
attribute [local simp] DeciSigma1.Semantics.Tree.le_top
attribute [local simp] DeciSigma1.Semantics.Tree.le_bot_iff
attribute [local simp] DeciSigma1.Semantics.Tree.top_le_iff
attribute [local simp] DeciSigma1.Semantics.Tree.node_le_node_iff

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}
namespace DeciSigma1.Semantics.Tree
theorem _root_.solution (t u : Tree n) :
    t ≤ u ↔ t = bot ∨ u = top ∨
      ∃ a b, t = node a ∧ u = node b ∧ ∀ i, a i ≤ b i := by
  constructor
  · intro h
    rcases t.eq_bot_or_eq_top_or_node with ht | ht | ⟨a, rfl⟩
    · exact Or.inl ht
    · subst t; exact Or.inr (Or.inl ((top_le_iff u).mp h))
    · rcases u.eq_bot_or_eq_top_or_node with hu | hu | ⟨b, rfl⟩
      · subst u; exact False.elim (node_ne_bot a ((le_bot_iff _).mp h))
      · exact Or.inr (Or.inl hu)
      · exact Or.inr (Or.inr ⟨a, b, rfl, rfl, (node_le_node_iff ..).mp h⟩)
  · rintro (rfl | rfl | ⟨a, b, rfl, rfl, h⟩)
    · exact bot_le u
    · exact le_top t
    · exact (node_le_node_iff ..).mpr h
end DeciSigma1.Semantics.Tree
