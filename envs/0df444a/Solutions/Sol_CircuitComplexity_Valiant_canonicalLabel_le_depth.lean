-- Prove2me | solution 1 for CircuitComplexity.Valiant.canonicalLabel_le_depth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:46.3408+00:00
-- url     : https://prove2.me/submissions/93adf591-206c-4c99-a863-b59016c0e4e2

module
public import Definitions.Def_LeanPool_CircuitComplexity_Digraph_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Valiant
section
@[expose] public section
namespace Digraph
end Digraph
namespace CircuitComplexity.Valiant
open Digraph
variable {V : Type*} [Fintype V]
omit [Fintype V] in
/-- The canonical-label set is bounded above by `Fintype.card V`: any
injective `Fin (n + 1) → V` forces `n + 1 ≤ Fintype.card V`. -/
private lemma canonicalLabel_set_bddAbove [Finite V] (G : Digraph V) (v : V) :
    BddAbove { n | ∃ p : Fin (n + 1) → V, G.IsSimplePath p ∧ p (Fin.last n) = v } := by
  have : Fintype V := Fintype.ofFinite V
  refine ⟨Fintype.card V, ?_⟩
  rintro n ⟨p, ⟨_, hinj⟩, _⟩
  have := Fintype.card_le_of_injective p hinj
  simp only [Fintype.card_fin] at this
  omega
omit [Fintype V] in
/-- The single-vertex path at `v` witnesses `0` in the canonical-label
edge-count set. -/
private lemma zero_mem_canonicalLabel_set (G : Digraph V) (v : V) :
    (0 : ℕ) ∈ { n | ∃ p : Fin (n + 1) → V, G.IsSimplePath p ∧ p (Fin.last n) = v } := by
  refine ⟨fun _ => v, ⟨fun i h => by omega, ?_⟩, rfl⟩
  intro a b _
  exact Fin.ext (by omega)
section LegalLabelHelpers
variable {V : Type*}
end LegalLabelHelpers
variable [DecidableEq V]
end CircuitComplexity.Valiant
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity CircuitComplexity.Valiant
open Digraph
variable {V : Type*} [Fintype V]
namespace CircuitComplexity.Valiant
theorem _root_.solution
    (G : Digraph V) (hac : IsAcyclic G) (v : V) :
    G.canonicalLabel v ≤ G.depth := by
  set S : Set ℕ := { n | ∃ p : Fin (n + 1) → V, G.IsSimplePath p ∧ p (Fin.last n) = v }
  change sSup S + 1 ≤ G.depth
  obtain ⟨p, ⟨hpath, _⟩, _⟩ :=
    Nat.sSup_mem ⟨0, zero_mem_canonicalLabel_set G v⟩ (canonicalLabel_set_bddAbove G v)
  exact le_csSup hac ⟨p, hpath⟩
end CircuitComplexity.Valiant
