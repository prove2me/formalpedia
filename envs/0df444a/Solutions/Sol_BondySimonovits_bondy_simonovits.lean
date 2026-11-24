-- Prove2me | solution 1 for BondySimonovits.bondy_simonovits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:19:33.401725+00:00
-- url     : https://prove2.me/submissions/be7ee76c-fada-4243-a90e-22b5ac04e927

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BSFinal
public import Definitions.Def_BondySimonovitsLib_BondySimonovits
public import Theorems.Thm_BondySimonovits_degree_sum_bound


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BondySimonovits
universe u
namespace BondySimonovits
theorem _root_.solution (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (∀ (v : V) (p : G.Walk v v), p.IsCycle → p.length ≠ 2 * k) →
      (G.edgeSet.ncard : ℝ) ≤ C * (Nat.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by
  refine ⟨16 * k + 4, fun V _ G hcyc => ?_⟩
  classical
  let _ : Fintype V := Fintype.ofFinite V
  have h := degree_sum_bound k hk G hcyc
  have hm : G.edgeSet.ncard = G.edgeFinset.card := Set.ncard_eq_toFinset_card' _
  have hsum : ∑ v, (Finset.univ.filter (G.Adj v)).card = 2 * G.edgeFinset.card := by
    rw [← sum_degrees_eq_twice_card_edges]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  rw [Nat.card_eq_fintype_card, hm]
  rw [hsum] at h
  push_cast at h
  linarith
end BondySimonovits
