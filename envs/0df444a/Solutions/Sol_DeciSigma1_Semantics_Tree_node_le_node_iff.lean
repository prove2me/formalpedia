-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.node_le_node_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:22.519463+00:00
-- url     : https://prove2.me/submissions/f5ddf989-41de-465b-bea6-d1df747a5506

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
theorem _root_.solution (a b : Fin n → Tree n) :
    node a ≤ node b ↔ ∀ i, a i ≤ b i := by
  constructor
  · intro h i w x y hx hy
    exact h (i :: w) x y hx hy
  · intro h w x y hx hy
    cases w with
    | nil => exact (Option.some.inj (hx.symm.trans hy)).le
    | cons i w => exact h i w x y hx hy
end DeciSigma1.Semantics.Tree
