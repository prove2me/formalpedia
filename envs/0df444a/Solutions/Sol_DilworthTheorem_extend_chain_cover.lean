-- Prove2me | solution 1 for DilworthTheorem.extend_chain_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:34:56.459517+00:00
-- url     : https://prove2.me/submissions/ea6435bd-5b58-4011-9022-487f1a2e25de

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

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution {m : ℕ} {S C : Finset α}
    (hCS : C ⊆ S) (hC_chain : IsChain (C : Set α))
    (C_prev : Fin m → Finset α) (hC_prev : IsChainCover (S \ C) C_prev) :
    ∃ D : Fin (m + 1) → Finset α, IsChainCover S D := by
  refine ⟨Fin.cons C C_prev, fun i => Fin.cases hC_chain (fun j => hC_prev.1 j) i, ?_, ?_⟩
  · ext x; simp only [mem_biUnion, mem_univ, true_and, Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ]
    have : (∃ i, x ∈ C_prev i) ↔ x ∈ S \ C := by rw [← hC_prev.2.1, mem_biUnion]; simp
    rw [this, mem_sdiff]
    exact ⟨by rintro (h | ⟨hS, -⟩); exact hCS h; exact hS, fun h => if hC : x ∈ C then Or.inl hC else Or.inr ⟨h, hC⟩⟩
  · intro i j hij; rw [disjoint_iff_ne]; rintro u hu v hv rfl
    induction' i using Fin.cases with i' <;> induction' j using Fin.cases with j'
    · exact (hij rfl).elim
    · rw [Fin.cons_zero] at hu; rw [Fin.cons_succ] at hv
      have : u ∈ S \ C := by rw [← hC_prev.2.1, mem_biUnion]; exact ⟨j', mem_univ j', hv⟩
      exact (mem_sdiff.mp this).2 hu
    · rw [Fin.cons_succ] at hu; rw [Fin.cons_zero] at hv
      have : u ∈ S \ C := by rw [← hC_prev.2.1, mem_biUnion]; exact ⟨i', mem_univ i', hu⟩
      exact (mem_sdiff.mp this).2 hv
    · rw [Fin.cons_succ] at hu; rw [Fin.cons_succ] at hv
      exact disjoint_left.mp (hC_prev.2.2 i' j' (fun h => hij (congr_arg Fin.succ h))) hu hv
end DilworthTheorem
