-- Prove2me | solution 1 for DegreeSequences.eg_necessary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:57:58.217107+00:00
-- url     : https://prove2.me/submissions/37b111bd-edff-4a9b-8713-65393b28e016

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Theorems.Thm_DegreeSequences_degree_eq_sum_ite

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    ∑ i with i.val < k, G.degree i ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (G.degree i) k := by
  set S : Finset (Fin n) := {i | i.val < k} with hSdef
  set T : Finset (Fin n) := {i | k ≤ i.val} with hTdef
  have hS : #S ≤ k := by rw [hSdef, Fin.card_filter_val_lt]; omega
  have hsplit : ∀ i, G.degree i = (∑ j ∈ S, if G.Adj i j then 1 else 0) +
      ∑ j ∈ T, if G.Adj i j then 1 else 0 := by
    intro i
    rw [degree_eq_sum_ite, ← Finset.sum_filter_add_sum_filter_not univ (fun j : Fin n => j.val < k)]
    simp only [not_lt, hSdef, hTdef]
  have h1 : ∑ i ∈ S, G.degree i = (∑ i ∈ S, ∑ j ∈ S, if G.Adj i j then 1 else 0) +
      ∑ i ∈ S, ∑ j ∈ T, if G.Adj i j then 1 else 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hsplit i
  have h2 : (∑ i ∈ S, ∑ j ∈ S, if G.Adj i j then 1 else 0) ≤ k * (k - 1) := by
    calc (∑ i ∈ S, ∑ j ∈ S, if G.Adj i j then 1 else 0) ≤ ∑ i ∈ S, (k - 1) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.sum_boole]
          have : ({j ∈ S | G.Adj i j} : Finset _) ⊆ S.erase i := by
            intro j hj
            rw [mem_filter] at hj
            exact mem_erase.mpr ⟨(G.ne_of_adj hj.2).symm, hj.1⟩
          have h := card_le_card this
          rw [card_erase_of_mem hi] at h
          simp only [Nat.cast_id]
          omega
      _ = #S * (k - 1) := by rw [sum_const, smul_eq_mul]
      _ ≤ k * (k - 1) := Nat.mul_le_mul_right _ hS
  have h3 : (∑ i ∈ S, ∑ j ∈ T, if G.Adj i j then 1 else 0) ≤ ∑ j ∈ T, min (G.degree j) k := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun j _ => ?_
    refine le_min ?_ ?_
    · rw [degree_eq_sum_ite]
      calc (∑ i ∈ S, if G.Adj i j then 1 else 0) = ∑ i ∈ S, if G.Adj j i then 1 else 0 := by
            simp only [G.adj_comm]
        _ ≤ ∑ i, if G.Adj j i then 1 else 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    · calc (∑ i ∈ S, if G.Adj i j then 1 else 0) ≤ ∑ i ∈ S, 1 :=
            Finset.sum_le_sum fun i _ => by split_ifs <;> simp
        _ = #S := by simp
        _ ≤ k := hS
  rw [h1]
  omega
end DegreeSequences
