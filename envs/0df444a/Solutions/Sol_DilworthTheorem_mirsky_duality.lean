-- Prove2me | solution 1 for DilworthTheorem.mirsky_duality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:30:42.208788+00:00
-- url     : https://prove2.me/submissions/fdbb91d3-5e6e-4d66-b103-0ee07f558d11

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
import Theorems.Thm_DilworthTheorem_mirsky_theorem

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution [Fintype α] (c : ℕ)
    (h_max : ∃ C : Finset α, IsChain (C : Set α) ∧ C.card = c)
    (h_bound : ∀ C : Finset α, IsChain (C : Set α) → C.card ≤ c) :
    (∃ A : Fin c → Finset α, IsAntichainCover Finset.univ A) ∧
    (∀ k < c, ¬ ∃ A : Fin k → Finset α, IsAntichainCover Finset.univ A) := by
  refine ⟨mirsky_theorem univ c (fun C _ => h_bound C), ?_⟩
  rintro k hk ⟨A, hA⟩
  rcases h_max with ⟨C, hC_chain, hC_card⟩
  have h_cov : C ⊆ Finset.biUnion Finset.univ (fun i => C ∩ A i) := fun x hx => by
    have : x ∈ Finset.biUnion univ A := by rw [hA.2.1]; exact mem_univ x
    rcases mem_biUnion.mp this with ⟨i, -, hi⟩
    exact mem_biUnion.mpr ⟨i, mem_univ i, mem_inter.mpr ⟨hx, hi⟩⟩
  have h_sum := (card_le_card h_cov).trans card_biUnion_le
  have h_sum_le : (Finset.univ : Finset (Fin k)).sum (fun i => (C ∩ A i).card) ≤ (Finset.univ : Finset (Fin k)).sum (fun _ => 1) :=
    sum_le_sum (fun i _ => chain_inter_antichain_card_le_one C (A i) hC_chain (hA.1 i))
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h_sum_le
  have : c ≤ k := hC_card ▸ h_sum.trans h_sum_le
  omega
end DilworthTheorem
