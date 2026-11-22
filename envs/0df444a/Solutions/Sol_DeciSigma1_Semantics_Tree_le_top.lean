-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.le_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:39.524405+00:00
-- url     : https://prove2.me/submissions/5542d9c5-1d6d-48c6-bf01-bdefbe8311c5

module
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Order.Lattice
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Theorems.Thm_DeciSigma1_Semantics_Tree_bot_le
attribute [local simp] DeciSigma1.Semantics.Tree.bot_le

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}
namespace DeciSigma1.Semantics.Tree
theorem _root_.solution (t : Tree n) : t ≤ top := by
  intro π a b ha hb
  cases π with
  | nil => simp only [top_fn_nil, Option.some.injEq] at hb; subst b; exact Sym.le_top a
  | cons i π => simp at hb
end DeciSigma1.Semantics.Tree
