-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.eq_bot_or_eq_top_or_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:47.261367+00:00
-- url     : https://prove2.me/submissions/bc6c6192-3db1-4d6e-9037-c2bc1711062a

module
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Order.Lattice
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Theorems.Thm_DeciSigma1_Semantics_Tree_eq_node_of_root_eq_f

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}
namespace DeciSigma1.Semantics.Tree
theorem _root_.solution (t : Tree n) :
    t = bot ∨ t = top ∨ ∃ a, t = node a := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp t.root_isSome
  cases s with
  | bot => exact Or.inl ((root_eq_bot_iff t).mp hs)
  | top => exact Or.inr (Or.inl ((root_eq_top_iff t).mp hs))
  | f => exact Or.inr (Or.inr ⟨_, t.eq_node_of_root_eq_f hs⟩)
end DeciSigma1.Semantics.Tree
