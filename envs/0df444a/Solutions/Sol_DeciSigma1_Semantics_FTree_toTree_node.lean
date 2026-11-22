-- Prove2me | solution 1 for DeciSigma1.Semantics.FTree.toTree_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:21.658409+00:00
-- url     : https://prove2.me/submissions/9d5fb376-c6ad-4369-b9e7-2bc2d4bc06df

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
theorem _root_.solution (a : Fin n → FTree n) :
    toTree (node a) = Tree.node (fun i => toTree (a i)) := rfl
end DeciSigma1.Semantics.FTree
