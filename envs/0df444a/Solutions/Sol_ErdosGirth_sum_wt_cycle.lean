-- Prove2me | solution 1 for ErdosGirth.sum_wt_cycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:30:59.062498+00:00
-- url     : https://prove2.me/submissions/0173dbb6-8c1a-4699-ba54-1547aa27b249

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
public import Theorems.Thm_ErdosGirth_sum_wt_subset
public import Theorems.Thm_ErdosGirth_edges_toFinset_subset_pairs

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
open Classical
namespace ErdosGirth
theorem _root_.solution {m : ℕ} (p : ℝ) {u : Fin m} (c : (⊤ : SimpleGraph (Fin m)).Walk u u) :
    ∑ S ∈ (pairs m).powerset, wt m p S * (if c.IsCycle ∧ c.edges.toFinset ⊆ S then 1 else 0)
      = if c.IsCycle then p ^ c.length else 0 := by
  by_cases hc : c.IsCycle
  · simp only [hc, true_and, ite_true, mul_ite, mul_one, mul_zero]
    rw [sum_wt_subset p (edges_toFinset_subset_pairs c), List.toFinset_card_of_nodup hc.edges_nodup,
      Walk.length_edges]
  · simp [hc]
end ErdosGirth
