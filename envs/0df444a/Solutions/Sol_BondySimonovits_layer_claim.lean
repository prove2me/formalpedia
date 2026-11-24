-- Prove2me | solution 1 for BondySimonovits.layer_claim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:14:29.130436+00:00
-- url     : https://prove2.me/submissions/6069b9d2-641d-490b-90ad-25a12d24e90b

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth
public import Theorems.Thm_BondySimonovits_ecount_comm
public import Theorems.Thm_BondySimonovits_ecount_union_left
public import Theorems.Thm_BondySimonovits_ecount_union_right
public import Theorems.Thm_BondySimonovits_ecount_eq_zero
public import Theorems.Thm_BondySimonovits_mem_layer
public import Theorems.Thm_BondySimonovits_layer_disjoint
public import Theorems.Thm_BondySimonovits_no_adj_same_layer
public import Theorems.Thm_BondySimonovits_cycle_of_dense
public import Theorems.Thm_BondySimonovits_exists_minimal_dense


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
variable (f : V → Bool) (hf : ∀ u v, K.Adj u v → f u ≠ f v)
include hf
namespace BondySimonovits
theorem _root_.solution (x : V) (k : ℕ) (hk : 2 ≤ k)
    (hcyc : ∀ (v : V) (p : K.Walk v v), p.IsCycle → p.length ≠ 2 * k) (i : ℕ) (hik : i + 1 ≤ k) :
    ecount K (layer K x i) (layer K x (i + 1)) ≤
      2 * k * ((layer K x i).card + (layer K x (i + 1)).card) := by
  by_contra hcon
  push Not at hcon
  set X := layer K x i ∪ layer K x (i + 1) with hX
  have hdisj := layer_disjoint K x (show i ≠ i + 1 by omega)
  have hXcard : X.card = (layer K x i).card + (layer K x (i + 1)).card :=
    Finset.card_union_of_disjoint hdisj
  have hXX : ecount K X X = 2 * ecount K (layer K x i) (layer K x (i + 1)) := by
    rw [hX, ecount_union_left K _ _ _ hdisj, ecount_union_right K _ _ _ hdisj,
      ecount_union_right K _ _ _ hdisj,
      ecount_eq_zero K _ _ (no_adj_same_layer K f hf x i),
      ecount_eq_zero K _ _ (no_adj_same_layer K f hf x (i + 1)),
      ecount_comm K (layer K x (i + 1)) (layer K x i)]
    ring
  obtain ⟨Y, hYX, hYne, hYdeg, hYmin⟩ := exists_minimal_dense K (2 * k) X
    (by rw [hXX, hXcard]; nlinarith)
  have hYL : ∀ v ∈ Y, K.Reachable x v ∧ (K.dist x v = i ∨ K.dist x v = i + 1) := by
    intro v hv
    rcases Finset.mem_union.1 (hYX hv) with h | h <;> rw [mem_layer] at h
    · exact ⟨h.1, Or.inl h.2⟩
    · exact ⟨h.1, Or.inr h.2⟩
  obtain ⟨v, p, hp, hpl⟩ := cycle_of_dense K f hf x k i hk hik Y hYL hYne hYdeg hYmin
  exact hcyc v p hp hpl
end BondySimonovits
