-- Prove2me | solution 1 for DilworthTheorem.dilworth_theorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:53:28.245056+00:00
-- url     : https://prove2.me/submissions/26a35ec5-cdd6-4840-aace-b8d2eb8d4ac8

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Antichain
import Mathlib.Tactic
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Theorems.Thm_DilworthTheorem_isChain_empty
import Theorems.Thm_DilworthTheorem_isAntichain_finset_singleton
import Theorems.Thm_DilworthTheorem_exists_maximal_chain
import Theorems.Thm_DilworthTheorem_lowerCone_subset
import Theorems.Thm_DilworthTheorem_upperCone_subset
import Theorems.Thm_DilworthTheorem_antichain_subset_lowerCone
import Theorems.Thm_DilworthTheorem_antichain_subset_upperCone
import Theorems.Thm_DilworthTheorem_lowerCone_inter_upperCone
import Theorems.Thm_DilworthTheorem_lowerCone_union_upperCone
import Theorems.Thm_DilworthTheorem_lowerCone_card_lt
import Theorems.Thm_DilworthTheorem_upperCone_card_lt
import Theorems.Thm_DilworthTheorem_align_chain_cover
import Theorems.Thm_DilworthTheorem_glue_chain_covers
import Theorems.Thm_DilworthTheorem_extend_chain_cover

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution (S : Finset α) (k : ℕ)
    (h_anti : ∀ A ⊆ S, IsAntichain (A : Set α) → A.card ≤ k) :
    ∃ C : Fin k → Finset α, IsChainCover S C := by
  have h_main : ∀ n (S : Finset α) k, S.card = n →
      (∀ A ⊆ S, IsAntichain (A : Set α) → A.card ≤ k) →
      ∃ C : Fin k → Finset α, IsChainCover S C := by
    intro n; induction' n using Nat.strong_induction_on with n ih
    intro S k hn h_anti
    by_cases hk0 : k = 0
    · subst hk0
      rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, by simp, fun i => Fin.elim0 i⟩
      · have := h_anti {x} (singleton_subset_iff.mpr hx) (isAntichain_finset_singleton x)
        simp at this
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      by_cases hn0 : n = 0
      · subst hn0; rw [Finset.card_eq_zero] at hn; subst hn
        refine ⟨fun _ => ∅, fun _ => by rw [coe_empty]; exact isChain_empty, by ext x; simp, fun _ _ _ => disjoint_empty_left _⟩
      · have hS_ne : S.Nonempty := card_pos.mp (by omega)
        rcases exists_maximal_chain S hS_ne with ⟨C, hCS, hC_ne, hC_chain, ⟨cmax, hcmax_in, hcmax_max⟩, ⟨cmin, hcmin_in, hcmin_min⟩⟩
        by_cases h_case1 : ∀ A ⊆ S \ C, IsAntichain (A : Set α) → A.card ≤ m
        · have h_card_lt : (S \ C).card < n := by
            rw [← hn, card_sdiff_of_subset hCS]; have : 0 < C.card := card_pos.mpr hC_ne; omega
          rcases ih (S \ C).card h_card_lt (S \ C) m rfl h_case1 with ⟨C_prev, hC_prev⟩
          exact extend_chain_cover hCS hC_chain C_prev hC_prev
        · have h_exists : ∃ A ⊆ S \ C, IsAntichain (A : Set α) ∧ m < A.card := by
            by_contra! h_all; exact h_case1 h_all
          rcases h_exists with ⟨A, hA_sub, hA_anti, hA_card_gt⟩
          have hAS : A ⊆ S := hA_sub.trans sdiff_subset
          have hA_card : A.card = m + 1 := by have := h_anti A hAS hA_anti; omega
          have hAC_disj : Disjoint A C := disjoint_left.mpr (fun a ha haC => (mem_sdiff.mp (hA_sub ha)).2 haC)
          have h_neg_lt : (lowerCone S A).card < n := hn ▸ lowerCone_card_lt hAS hCS hcmax_in hcmax_max hAC_disj
          have h_pos_lt : (upperCone S A).card < n := hn ▸ upperCone_card_lt hAS hCS hcmin_in hcmin_min hAC_disj
          rcases ih _ h_neg_lt (lowerCone S A) (m + 1) rfl (fun B hB => h_anti B (hB.trans (lowerCone_subset S A))) with ⟨C_neg, hC_neg⟩
          rcases ih _ h_pos_lt (upperCone S A) (m + 1) rfl (fun B hB => h_anti B (hB.trans (upperCone_subset S A))) with ⟨C_pos, hC_pos⟩
          let e_equiv : Fin (m + 1) ≃ {x // x ∈ A} := (Fin.castOrderIso hA_card.symm).toEquiv.trans (Finset.equivFin A).symm
          let e : Fin (m + 1) → α := fun i => (e_equiv i).1
          have he_inj : Function.Injective e := fun i1 i2 h => e_equiv.injective (Subtype.ext h)
          have he_mem : ∀ i, e i ∈ A := fun i => (e_equiv i).2
          rcases align_chain_cover (antichain_subset_lowerCone hAS) hA_anti e he_inj he_mem hC_neg with ⟨D_neg, hD_neg, h_mem_neg⟩
          rcases align_chain_cover (antichain_subset_upperCone hAS) hA_anti e he_inj he_mem hC_pos with ⟨D_pos, hD_pos, h_mem_pos⟩
          exact glue_chain_covers hA_anti hAS
            (lowerCone_union_upperCone S A (m + 1) hAS hA_anti hA_card h_anti)
            (lowerCone_inter_upperCone hA_anti hAS) e he_mem D_neg hD_neg h_mem_neg D_pos hD_pos h_mem_pos
  exact h_main S.card S k rfl h_anti
end DilworthTheorem
