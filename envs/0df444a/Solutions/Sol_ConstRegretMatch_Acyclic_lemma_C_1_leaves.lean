-- Prove2me | solution 1 for ConstRegretMatch.Acyclic.lemma_C_1_leaves
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:35:32.458656+00:00
-- url     : https://prove2.me/submissions/303ba78c-8d84-46a0-9cdd-2d1a086b8b5a

import Mathlib
import Definitions.Def_ConstRegretMatch_Acyclic_Network

set_option autoImplicit false
open ConstRegretMatch.Acyclic

theorem solution {n d : ℕ} (N : MatchingNetwork n d)
    (hconn : (networkGraph N).Connected) (hacyc : (networkGraph N).IsAcyclic) :
    n + 1 ≤ (leaves (networkGraph N)).card + d := by
  classical
  set G := networkGraph N with hG
  have htree : G.IsTree := ⟨hconn, hacyc⟩
  have hedge := htree.card_edgeFinset
  have hsum := G.sum_degrees_eq_twice_card_edges
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hedge
  -- degrees
  have hdegr : ∀ m : Fin d, G.degree (Sum.inr m) = (N.A m).card := by
    intro m
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : G.neighborFinset (Sum.inr m) = (N.A m).map ⟨Sum.inl, Sum.inl_injective⟩ := by
      ext v
      cases v <;> simp [SimpleGraph.mem_neighborFinset, hG, networkGraph, incidenceGraph]
    rw [this, Finset.card_map]
  have hdegl : ∀ i : Fin n, G.degree (Sum.inl i) = (Finset.univ.filter (fun m => i ∈ N.A m)).card := by
    intro i
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : G.neighborFinset (Sum.inl i) =
        (Finset.univ.filter (fun m => i ∈ N.A m)).map ⟨Sum.inr, Sum.inr_injective⟩ := by
      ext v
      cases v <;> simp [SimpleGraph.mem_neighborFinset, hG, networkGraph, incidenceGraph]
    rw [this, Finset.card_map]
  -- double counting
  have hdc : ∑ i : Fin n, (Finset.univ.filter (fun m => i ∈ N.A m)).card = ∑ m : Fin d, (N.A m).card := by
    have e1 : ∀ i : Fin n, (Finset.univ.filter (fun m => i ∈ N.A m)).card =
        ∑ m : Fin d, (if i ∈ N.A m then 1 else 0) := by
      intro i; rw [Finset.sum_boole]; simp only [Nat.cast_id]
    have e2 : ∀ m : Fin d, (N.A m).card = ∑ i : Fin n, (if i ∈ N.A m then 1 else 0) := by
      intro m
      rw [Finset.sum_boole]
      simp only [Nat.cast_id]
      congr 1
      ext i; simp
    simp only [e1, e2]
    rw [Finset.sum_comm]
  rw [Fintype.sum_sum_type] at hsum
  simp only [hdegr, hdegl] at hsum
  rw [← hdc] at hsum
  -- c_i ≥ 1
  have hc1 : ∀ i : Fin n, 1 ≤ (Finset.univ.filter (fun m => i ∈ N.A m)).card := by
    intro i
    obtain ⟨m, hm⟩ := N.covers i
    exact Finset.card_pos.mpr ⟨m, by simp [hm]⟩
  -- leaves
  have hleaves : (leaves G) = (Finset.univ.filter (fun i : Fin n =>
      (Finset.univ.filter (fun m => i ∈ N.A m)).card = 1)).map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext v
    cases v with
    | inl i => simp [leaves, hdegl]
    | inr m =>
      have := N.two_le_card m
      simp [leaves, hdegr]
      omega
  rw [hleaves, Finset.card_map]
  set c : Fin n → ℕ := fun i => (Finset.univ.filter (fun m => i ∈ N.A m)).card with hc
  have hc1' : ∀ i : Fin n, 1 ≤ c i := fun i => hc1 i
  have hsum' : (∑ i : Fin n, c i) + (∑ i : Fin n, c i) = 2 * G.edgeFinset.card := hsum
  have key : ∀ i : Fin n, 2 ≤ c i + (if c i = 1 then 1 else 0) := by
    intro i
    have := hc1' i
    split_ifs with h <;> omega
  have hS : ∑ i : Fin n, (2 : ℕ) ≤ ∑ i : Fin n, (c i + (if c i = 1 then 1 else 0)) :=
    Finset.sum_le_sum fun i _ => key i
  have hL : ∑ i : Fin n, (if c i = 1 then 1 else 0) =
      (Finset.univ.filter (fun i : Fin n => c i = 1)).card := by
    rw [Finset.sum_boole]; simp only [Nat.cast_id]
  have hLeq : (Finset.univ.filter (fun i : Fin n => (Finset.univ.filter (fun m => i ∈ N.A m)).card = 1)).card =
      (Finset.univ.filter (fun i : Fin n => c i = 1)).card := rfl
  rw [Finset.sum_add_distrib, hL] at hS
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hS
  omega
