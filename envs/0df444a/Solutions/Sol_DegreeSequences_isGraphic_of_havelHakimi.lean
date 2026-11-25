-- Prove2me | solution 1 for DegreeSequences.isGraphic_of_havelHakimi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:08:03.994215+00:00
-- url     : https://prove2.me/submissions/255e1c50-32e5-4c89-ba14-b7179c0ba6e0

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Theorems.Thm_DegreeSequences_degree_fin_succ
public import Theorems.Thm_DegreeSequences_hhExtend_adj_zero_zero
public import Theorems.Thm_DegreeSequences_hhExtend_adj_zero_succ
public import Theorems.Thm_DegreeSequences_hhExtend_adj_succ_succ

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {m : ℕ} (d : Fin (m + 1) → ℕ) (h0 : d 0 ≤ m)
    (hpos : ∀ j : Fin m, j.val < d 0 → 1 ≤ d j.succ) (hH : IsGraphic (havelHakimi d)) :
    IsGraphic d := by
  classical
  obtain ⟨H, _, hH⟩ := hH
  refine ⟨hhExtend d H, inferInstance, fun v => ?_⟩
  rw [degree_fin_succ]
  induction v using Fin.cases with
  | zero =>
    simp only [hhExtend_adj_zero_zero, ite_false, zero_add, hhExtend_adj_zero_succ]
    rw [Fin.card_filter_val_lt]
    omega
  | succ j =>
    have h1 : (hhExtend d H).Adj j.succ 0 ↔ j.val < d 0 := by
      rw [(hhExtend d H).adj_comm, hhExtend_adj_zero_succ]
    simp only [h1, hhExtend_adj_succ_succ]
    have h2 : #{k : Fin m | H.Adj j k} = H.degree j := by
      rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    rw [h2, hH j]
    unfold havelHakimi
    have := hpos j
    split_ifs <;> omega
end DegreeSequences
