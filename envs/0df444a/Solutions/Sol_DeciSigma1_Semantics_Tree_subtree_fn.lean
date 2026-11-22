-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.subtree_fn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:38:16.910001+00:00
-- url     : https://prove2.me/submissions/3b77351b-6bcc-4cb5-9fbd-13c0c6a8f462

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
theorem _root_.solution {t u : Tree n} {π : List (Fin n)} (h : t.subtree π = some u)
    (ρ : List (Fin n)) : u.fn ρ = t.fn (π ++ ρ) := by
  unfold subtree at h
  split at h
  · cases Option.some.inj h
    rfl
  · contradiction
end DeciSigma1.Semantics.Tree
