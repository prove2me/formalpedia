-- Prove2me | solution 1 for DilworthTheorem.dilworth_duality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:57:19.01518+00:00
-- url     : https://prove2.me/submissions/d074b174-74f1-47b4-a66b-ae0d6fed9bd2

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
import Theorems.Thm_DilworthTheorem_chain_inter_antichain_card_le_one
import Theorems.Thm_DilworthTheorem_dilworth_theorem

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution [Fintype α] (w : ℕ)
    (h_max : ∃ A : Finset α, IsAntichain (A : Set α) ∧ A.card = w)
    (h_bound : ∀ A : Finset α, IsAntichain (A : Set α) → A.card ≤ w) :
    (∃ C : Fin w → Finset α, IsChainCover Finset.univ C) ∧
    (∀ k < w, ¬ ∃ C : Fin k → Finset α, IsChainCover Finset.univ C) := by
  refine ⟨dilworth_theorem univ w (fun A _ => h_bound A), ?_⟩
  rintro k hk ⟨C, hC⟩
  rcases h_max with ⟨A, hA_anti, hA_card⟩
  have h_cov : A ⊆ Finset.biUnion Finset.univ (fun i => A ∩ C i) := fun x hx => by
    have : x ∈ Finset.biUnion univ C := by rw [hC.2.1]; exact mem_univ x
    rcases mem_biUnion.mp this with ⟨i, -, hi⟩
    exact mem_biUnion.mpr ⟨i, mem_univ i, mem_inter.mpr ⟨hx, hi⟩⟩
  have h_sum := (card_le_card h_cov).trans card_biUnion_le
  have h_sum_le : (Finset.univ : Finset (Fin k)).sum (fun i => (A ∩ C i).card) ≤ (Finset.univ : Finset (Fin k)).sum (fun _ => 1) :=
    sum_le_sum (fun i _ => by rw [inter_comm]; exact chain_inter_antichain_card_le_one (C i) A (hC.1 i) hA_anti)
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h_sum_le
  have : w ≤ k := hA_card ▸ h_sum.trans h_sum_le
  omega
end DilworthTheorem
