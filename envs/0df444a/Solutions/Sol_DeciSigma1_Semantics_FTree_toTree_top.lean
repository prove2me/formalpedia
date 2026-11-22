-- Prove2me | solution 1 for DeciSigma1.Semantics.FTree.toTree_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:41.724832+00:00
-- url     : https://prove2.me/submissions/25ce2bbf-8e4a-44e3-b9e5-f3e014f16520

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
open DeciSigma1.Semantics.FTree
variable {n : ℕ}
namespace DeciSigma1.Semantics.FTree
theorem _root_.solution : toTree (top : FTree n) = Tree.top := rfl
end DeciSigma1.Semantics.FTree
