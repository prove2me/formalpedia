-- Prove2me | solution 1 for DegreeSequences.havelHakimi_of_isGraphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:51:33.78436+00:00
-- url     : https://prove2.me/submissions/c1027dff-9832-4faf-bd11-475545ae45c8

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Theorems.Thm_DegreeSequences_degree_fin_succ
public import Theorems.Thm_DegreeSequences_mem_hhSet
public import Theorems.Thm_DegreeSequences_card_hhSet
public import Theorems.Thm_DegreeSequences_hh_forward_aux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {m : ℕ} (d : Fin (m + 1) → ℕ) (hd : Antitone d)
    (hG : IsGraphic d) :
    d 0 ≤ m ∧ (∀ j : Fin m, j.val < d 0 → 1 ≤ d j.succ) ∧ IsGraphic (havelHakimi d) := by
  classical
  obtain ⟨G, _, hG⟩ := hG
  have h0 : d 0 ≤ m := by
    have := G.degree_lt_card_verts 0
    rw [hG, Fintype.card_fin] at this
    omega
  obtain ⟨G', _, hdeg, hadj⟩ := hh_forward_aux d hd h0 _ G inferInstance hG le_rfl
  have hN : G'.neighborFinset 0 = hhSet d := by
    symm
    refine eq_of_subset_of_card_le (fun v hv => (mem_neighborFinset _ _ _).mpr (hadj v hv)) ?_
    rw [card_neighborFinset_eq_degree, hdeg, card_hhSet d h0]
  have hj : ∀ j : Fin m, G'.Adj j.succ 0 ↔ j.val < d 0 := by
    intro j
    rw [G'.adj_comm, ← mem_neighborFinset, hN, mem_hhSet, Fin.val_succ]
    simp [Fin.succ_ne_zero]
  have hdj : ∀ j : Fin m,
      d j.succ = (if j.val < d 0 then 1 else 0) + #{k : Fin m | G'.Adj j.succ k.succ} := by
    intro j
    rw [← hdeg, degree_fin_succ]
    simp only [hj]
  refine ⟨h0, fun j hj' => ?_, G'.comap Fin.succ, inferInstance, fun j => ?_⟩
  · rw [hdj j]; simp only [hj', ite_true]; omega
  · rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    simp only [comap_adj]
    unfold havelHakimi
    rw [hdj j]
    split_ifs <;> simp
end DegreeSequences
