-- Prove2me | solution 1 for DilworthTheorem.glue_chain_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:49:22.497774+00:00
-- url     : https://prove2.me/submissions/a2165b4f-2b29-41b2-b2b7-ccc8ea5811ec

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
import Theorems.Thm_DilworthTheorem_lowerCone_chain_le
import Theorems.Thm_DilworthTheorem_upperCone_chain_le
import Theorems.Thm_DilworthTheorem_cover_inter_antichain_eq

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution {k : ℕ} {S A : Finset α}
    (hA_anti : IsAntichain (A : Set α)) (_hAS : A ⊆ S)
    (h_union : lowerCone S A ∪ upperCone S A = S)
    (h_inter : lowerCone S A ∩ upperCone S A = A)
    (e : Fin k → α) (he_mem : ∀ i, e i ∈ A)
    (D_neg : Fin k → Finset α) (hD_neg : IsChainCover (lowerCone S A) D_neg) (h_mem_neg : ∀ i, e i ∈ D_neg i)
    (D_pos : Fin k → Finset α) (hD_pos : IsChainCover (upperCone S A) D_pos) (h_mem_pos : ∀ i, e i ∈ D_pos i) :
    ∃ C : Fin k → Finset α, IsChainCover S C := by
  let C : Fin k → Finset α := fun i => D_neg i ∪ D_pos i
  have hD_neg_sub : ∀ i, D_neg i ⊆ lowerCone S A := fun i x hx => by rw [← hD_neg.2.1, mem_biUnion]; exact ⟨i, mem_univ i, hx⟩
  have hD_pos_sub : ∀ i, D_pos i ⊆ upperCone S A := fun i x hx => by rw [← hD_pos.2.1, mem_biUnion]; exact ⟨i, mem_univ i, hx⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro i u v hu hv
    simp only [mem_coe, mem_union, C] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact hD_neg.1 i u v hu hv
    · have hu_le := lowerCone_chain_le (hD_neg.1 i) hA_anti (h_mem_neg i) (he_mem i) hu (mem_filter.mp (hD_neg_sub i hu)).2
      have hv_ge := upperCone_chain_le (hD_pos.1 i) hA_anti (h_mem_pos i) (he_mem i) hv (mem_filter.mp (hD_pos_sub i hv)).2
      exact Or.inl (hu_le.trans hv_ge)
    · have hu_ge := upperCone_chain_le (hD_pos.1 i) hA_anti (h_mem_pos i) (he_mem i) hu (mem_filter.mp (hD_pos_sub i hu)).2
      have hv_le := lowerCone_chain_le (hD_neg.1 i) hA_anti (h_mem_neg i) (he_mem i) hv (mem_filter.mp (hD_neg_sub i hv)).2
      exact Or.inr (hv_le.trans hu_ge)
    · exact hD_pos.1 i u v hu hv
  · rw [← h_union, ← hD_neg.2.1, ← hD_pos.2.1]
    ext x; simp only [mem_biUnion, mem_univ, true_and, mem_union, C]
    exact ⟨fun ⟨i, hi⟩ => hi.elim (fun h => Or.inl ⟨i, h⟩) (fun h => Or.inr ⟨i, h⟩),
           fun h => h.elim (fun ⟨i, h⟩ => ⟨i, Or.inl h⟩) (fun ⟨i, h⟩ => ⟨i, Or.inr h⟩)⟩
  · intro i j hij
    rw [disjoint_iff_ne]; rintro u hu _ hv rfl
    have hu_sub : ∀ k, u ∈ D_neg k ∪ D_pos k → (u ∈ lowerCone S A → u ∈ D_neg k) ∧ (u ∈ upperCone S A → u ∈ D_pos k) := by
      intro k hk; rcases mem_union.mp hk with h | h
      · exact ⟨fun _ => h, fun hpos => by
          have huA : u ∈ A := by rw [← h_inter, mem_inter]; exact ⟨(hD_neg_sub k) h, hpos⟩
          have := cover_inter_antichain_eq (hD_neg.1 k) hA_anti (h_mem_neg k) (he_mem k) h huA
          exact this ▸ h_mem_pos k⟩
      · exact ⟨fun hneg => by
          have huA : u ∈ A := by rw [← h_inter, mem_inter]; exact ⟨hneg, (hD_pos_sub k) h⟩
          have := cover_inter_antichain_eq (hD_pos.1 k) hA_anti (h_mem_pos k) (he_mem k) h huA
          exact this ▸ h_mem_neg k, fun _ => h⟩
    rcases (mem_union.mp hu).elim (fun h => Or.inl (hD_neg_sub i h)) (fun h => Or.inr (hD_pos_sub i h)) with hneg | hpos
    · exact (disjoint_left.mp (hD_neg.2.2 i j hij) ((hu_sub i hu).1 hneg)) ((hu_sub j hv).1 hneg)
    · exact (disjoint_left.mp (hD_pos.2.2 i j hij) ((hu_sub i hu).2 hpos)) ((hu_sub j hv).2 hpos)
end DilworthTheorem
