-- Prove2me | solution 1 for DilworthTheorem.mirsky_theorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:46:18.60456+00:00
-- url     : https://prove2.me/submissions/d0b3bfea-0fd0-4be2-b942-c5e052403730

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
import Theorems.Thm_DilworthTheorem_isAntichain_empty
import Theorems.Thm_DilworthTheorem_posetHeight_ge_one
import Theorems.Thm_DilworthTheorem_posetHeight_le
import Theorems.Thm_DilworthTheorem_posetHeight_lt_of_lt

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution (S : Finset α) (m : ℕ)
    (h_chain : ∀ C ⊆ S, IsChain (C : Set α) → C.card ≤ m) :
    ∃ A : Fin m → Finset α, IsAntichainCover S A := by
  by_cases hm : m = 0
  · subst hm
    have : S = ∅ := by
      by_contra! h; rcases h with ⟨x, hx⟩
      have := (posetHeight_ge_one hx).trans (posetHeight_le h_chain (x := x)); omega
    subst this
    refine ⟨fun _ => ∅, fun _ => by rw [coe_empty]; exact isAntichain_empty, by simp, fun _ _ _ => disjoint_empty_left _⟩
  · let A : Fin m → Finset α := fun i => S.filter (fun x => posetHeight S x = i.val + 1)
    refine ⟨A, ?_, ?_, ?_⟩
    · intro i u v hu hv hne
      simp only [mem_coe, mem_filter, A] at hu hv
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := posetHeight_lt_of_lt hu.1 hv.1 (lt_of_le_of_ne h hne); omega
      · have := posetHeight_lt_of_lt hv.1 hu.1 (lt_of_le_of_ne h hne.symm); omega
    · ext x; simp only [mem_biUnion, mem_univ, true_and, mem_filter, A]
      refine ⟨fun ⟨i, hxS, _⟩ => hxS, fun hxS => ?_⟩
      have h1 := posetHeight_ge_one hxS
      have hm_ge := posetHeight_le h_chain (x := x)
      exact ⟨⟨posetHeight S x - 1, by omega⟩, hxS, by dsimp; omega⟩
    · intro i j hij
      rw [disjoint_iff_ne]; rintro u hu _ hv rfl
      simp only [mem_filter, A] at hu hv
      exact hij (Fin.ext (by omega))
end DilworthTheorem
