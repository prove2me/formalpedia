-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.le_bot_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:40.253387+00:00
-- url     : https://prove2.me/submissions/3d84db55-b7b9-4baf-8fb3-9c77de5e1d45

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
theorem _root_.solution (t : Tree n) : t ≤ bot ↔ t = bot :=
  ⟨fun h => le_antisymm h (bot_le t), fun h => h ▸ le_refl bot⟩
end DeciSigma1.Semantics.Tree
