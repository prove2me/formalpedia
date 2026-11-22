-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.label_eq_f_of_proper_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:39:04.772447+00:00
-- url     : https://prove2.me/submissions/0f4ea9b5-83e3-4fa4-9d67-8eed6f91ddd6

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
theorem _root_.solution (t : Tree n) {π ρ : List (Fin n)}
    (hprefix : π.IsPrefix ρ) (hne : π ≠ ρ) (h : (t.fn ρ).isSome) :
    t.fn π = some Sym.f := by
  obtain ⟨σ, rfl⟩ := hprefix
  cases σ with
  | nil => simp at hne
  | cons i σ =>
    apply (t.child_isSome_iff π i).mp
    exact t.domain_append_left (π ++ [i]) σ (by simpa [List.append_assoc] using h)
end DeciSigma1.Semantics.Tree
