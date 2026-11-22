-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.bot_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:20.827677+00:00
-- url     : https://prove2.me/submissions/fe587930-2ada-41b5-9a00-c52d292fa38c

module
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Order.Lattice
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}
namespace DeciSigma1.Semantics.Tree
theorem _root_.solution (t : Tree n) : bot ≤ t := by
  intro π a b ha hb
  cases π with
  | nil => simp only [bot_fn_nil, Option.some.injEq] at ha; subst a; exact Sym.bot_le b
  | cons i π => simp at ha
end DeciSigma1.Semantics.Tree
