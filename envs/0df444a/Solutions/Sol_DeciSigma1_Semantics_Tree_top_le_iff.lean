-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.top_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:34:07.119845+00:00
-- url     : https://prove2.me/submissions/bc761e1f-0b4c-49c4-9024-7ad5137adf81

module
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Order.Lattice
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_top
attribute [local simp] DeciSigma1.Semantics.Tree.le_top

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}
namespace DeciSigma1.Semantics.Tree
theorem _root_.solution (t : Tree n) : top ≤ t ↔ t = top :=
  ⟨fun h => le_antisymm (le_top t) h, fun h => h ▸ le_refl top⟩
end DeciSigma1.Semantics.Tree
