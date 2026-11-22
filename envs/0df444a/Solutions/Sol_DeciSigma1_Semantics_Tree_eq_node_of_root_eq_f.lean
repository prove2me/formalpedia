-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.eq_node_of_root_eq_f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:22.21619+00:00
-- url     : https://prove2.me/submissions/1aedbe5b-c65e-4e91-aca7-cc39844185fe

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
theorem _root_.solution (t : Tree n) (h : t.fn [] = some Sym.f) :
    t = node (fun i => t.branch i h) := by
  apply ext
  funext π
  cases π with
  | nil => exact h
  | cons i π => rfl
end DeciSigma1.Semantics.Tree
