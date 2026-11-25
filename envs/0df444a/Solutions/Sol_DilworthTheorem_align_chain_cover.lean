-- Prove2me | solution 1 for DilworthTheorem.align_chain_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:34:07.930805+00:00
-- url     : https://prove2.me/submissions/5c3b6adc-091a-4131-bd4e-3e82ffa16d6a

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
import Theorems.Thm_DilworthTheorem_chain_inter_antichain_subsingleton

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution {k : ℕ} {T A : Finset α} (hAT : A ⊆ T) (hA_anti : IsAntichain (A : Set α))
    (e : Fin k → α) (he_inj : Function.Injective e) (he_mem : ∀ i, e i ∈ A)
    {C : Fin k → Finset α} (hC : IsChainCover T C) :
    ∃ D : Fin k → Finset α, IsChainCover T D ∧ (∀ i, e i ∈ D i) := by
  have h_ex : ∀ i : Fin k, ∃ j : Fin k, e i ∈ C j := by
    intro i; have : e i ∈ Finset.biUnion Finset.univ C := by rw [hC.2.1]; exact hAT (he_mem i)
    simpa [mem_biUnion] using this
  let tau : Fin k → Fin k := fun i => (h_ex i).choose
  have htau_mem : ∀ i, e i ∈ C (tau i) := fun i => (h_ex i).choose_spec
  have htau_inj : Function.Injective tau := by
    intro i1 i2 h
    have heq := chain_inter_antichain_subsingleton (C (tau i1)) A (hC.1 (tau i1)) hA_anti (e i1) (e i2)
      ⟨htau_mem i1, he_mem i1⟩ ⟨h ▸ htau_mem i2, he_mem i2⟩
    exact he_inj heq
  have htau_bi : Function.Bijective tau := (Fintype.bijective_iff_injective_and_card tau).mpr ⟨htau_inj, rfl⟩
  refine ⟨C ∘ tau, ⟨fun i => hC.1 (tau i), ?_, fun i j hij => hC.2.2 (tau i) (tau j) (fun h => hij (htau_inj h))⟩, htau_mem⟩
  rw [← hC.2.1]
  ext x; simp only [mem_biUnion, mem_univ, true_and, Function.comp_apply]
  exact ⟨fun ⟨i, hi⟩ => ⟨tau i, hi⟩, fun ⟨j, hj⟩ => by rcases htau_bi.2 j with ⟨i, rfl⟩; exact ⟨i, hj⟩⟩
end DilworthTheorem
