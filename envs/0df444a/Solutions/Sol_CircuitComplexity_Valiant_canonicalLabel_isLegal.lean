-- Prove2me | solution 1 for CircuitComplexity.Valiant.canonicalLabel_isLegal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:49.492342+00:00
-- url     : https://prove2.me/submissions/62a506c9-f8a2-48c6-8210-8901fde4d71d

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
omit [Fintype V] in
/-- **Cycle contradiction.** A simple path `p` of length `m` ending at `u`,
together with an edge `u → v` and an occurrence of `v` within `p`, closes
a cycle. We can then build directed walks of arbitrary length by repeatedly
going around the cycle, so `G` is not acyclic. -/
private lemma not_acyclic_of_cycle_witness
    (G : Digraph V) {u v : V} (huv : G.Adj u v)
    {m : ℕ} (p : Fin m → V) (hpath : G.IsDirectedPath p)
    (iu iv : Fin m) (hpu : p iu = u) (hiu : iu.val + 1 = m) (hpv : p iv = v) :
    ¬ IsAcyclic G := by
  rw [IsAcyclic, not_bddAbove_iff]
  intro N
  have hiv_lt_m : iv.val < m := iv.isLt
  have hL_pos : 0 < m - iv.val := by omega
  have h_bnd : ∀ j : ℕ, iv.val + j % (m - iv.val) < m := fun j => by
    have := Nat.mod_lt j hL_pos; omega
  refine ⟨N + 1,
    ⟨fun k : Fin (N + 1) => p ⟨iv.val + k.val % (m - iv.val), h_bnd k.val⟩, ?_⟩,
    Nat.lt_succ_self _⟩
  intro k hk
  have h_a_lt : k.val % (m - iv.val) < m - iv.val := Nat.mod_lt _ hL_pos
  have h_add_mod : (k.val + 1) % (m - iv.val) =
      (k.val % (m - iv.val) + 1) % (m - iv.val) := by
    simp_all
  by_cases hwrap : k.val % (m - iv.val) + 1 = m - iv.val
  · have h_next : (k.val + 1) % (m - iv.val) = 0 := by
      rw [h_add_mod, hwrap, Nat.mod_self]
    have h_a_eq : k.val % (m - iv.val) = m - iv.val - 1 := by omega
    have hu_eq : p ⟨iv.val + k.val % (m - iv.val), h_bnd k.val⟩ = u := by
      have hval : iv.val + k.val % (m - iv.val) = iu.val := by omega
      rw [show (⟨iv.val + k.val % (m - iv.val), h_bnd k.val⟩ : Fin m) = iu from
        Fin.ext hval, hpu]
    have hv_eq : p ⟨iv.val + (k.val + 1) % (m - iv.val), h_bnd (k.val + 1)⟩ = v := by
      have : (⟨iv.val + (k.val + 1) % (m - iv.val), h_bnd (k.val + 1)⟩ : Fin m) = iv := by
        apply Fin.ext
        change iv.val + (k.val + 1) % (m - iv.val) = iv.val
        rw [h_next]; rfl
      rw [this, hpv]
    change G.Adj (p ⟨iv.val + k.val % (m - iv.val), h_bnd k.val⟩)
               (p ⟨iv.val + (k.val + 1) % (m - iv.val), h_bnd (k.val + 1)⟩)
    rw [hu_eq, hv_eq]
    exact huv
  · have hlt : k.val % (m - iv.val) + 1 < m - iv.val := by omega
    have h_next : (k.val + 1) % (m - iv.val) = k.val % (m - iv.val) + 1 := by
      rw [h_add_mod, Nat.mod_eq_of_lt hlt]
    have hbnd2 : iv.val + k.val % (m - iv.val) + 1 < m := by omega
    have step := hpath ⟨iv.val + k.val % (m - iv.val), h_bnd k.val⟩ hbnd2
    have h_target :
        (⟨iv.val + (k.val + 1) % (m - iv.val), h_bnd (k.val + 1)⟩ : Fin m) =
        ⟨iv.val + k.val % (m - iv.val) + 1, hbnd2⟩ := by
      apply Fin.ext
      change iv.val + (k.val + 1) % (m - iv.val) = iv.val + k.val % (m - iv.val) + 1
      omega
    simp_all
omit [Fintype V] in
/-- **Extending a simple path by an edge.** In an acyclic digraph, a
simple path `p` ending at `u` followed by an edge `u → v` yields a
simple path ending at `v` that is one longer. -/
private lemma extend_simple_path (G : Digraph V) (hac : IsAcyclic G)
    {u v : V} (huv : G.Adj u v) {n : ℕ} {p : Fin (n + 1) → V}
    (hsp : G.IsSimplePath p) (hpu : p (Fin.last n) = u) :
    ∃ p' : Fin (n + 2) → V, G.IsSimplePath p' ∧ p' (Fin.last (n + 1)) = v := by
  classical
  obtain ⟨hpath, hinj⟩ := hsp
  have hv_notin : ∀ i : Fin (n + 1), p i ≠ v := fun i hpv =>
    not_acyclic_of_cycle_witness G huv p hpath (Fin.last n) i hpu rfl hpv hac
  refine ⟨fun k => if h : k.val < n + 1 then p ⟨k.val, h⟩ else v, ⟨?_, ?_⟩, ?_⟩
  · intro k hk
    dsimp only
    split_ifs with h₁ h₂
    · exact hpath ⟨k.val, h₁⟩ h₂
    · have heq : (⟨k.val, h₁⟩ : Fin (n + 1)) = Fin.last n := by
        apply Fin.ext; change k.val = n; omega
      rw [heq, hpu]; exact huv
    · omega
    · omega
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    dsimp only at hab
    split_ifs at hab with h₁ h₂ h₃
    · apply Fin.ext; exact Fin.mk_eq_mk.mp (hinj hab)
    · exact absurd hab (hv_notin ⟨a, h₁⟩)
    · exact absurd hab.symm (hv_notin ⟨b, h₃⟩)
    · apply Fin.ext; change a = b; omega
  · simp_all
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
theorem _root_.solution (G : Digraph V) (hac : IsAcyclic G) :
    IsLegalLabeling G G.canonicalLabel := by
  classical
  intro u v huv
  obtain ⟨p, hsp, hpu⟩ :=
    Nat.sSup_mem ⟨0, zero_mem_canonicalLabel_set G u⟩ (canonicalLabel_set_bddAbove G u)
  obtain ⟨p', hsp', hend⟩ := extend_simple_path G hac huv hsp hpu
  have hle := le_csSup (canonicalLabel_set_bddAbove G v) ⟨p', hsp', hend⟩
  change _ + 1 < _ + 1
  omega
end CircuitComplexity.Valiant
