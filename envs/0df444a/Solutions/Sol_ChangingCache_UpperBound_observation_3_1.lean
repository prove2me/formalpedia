-- Prove2me | solution 1 for ChangingCache.UpperBound.observation_3_1
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T16:47:48.573064+00:00
-- url     : https://prove2.me/submissions/0b503197-bf78-458b-a5d1-e927ff293967

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Model

open ChangingCache.UpperBound

namespace Obs31Aux

variable {α : Type*} [DecidableEq α]

theorem missB_take (σ : List α) (T : ℕ → Finset α) {r i : ℕ} (hi : i < r) :
    missB (σ.take r) T i = missB σ T i := by
  unfold missB
  rw [List.getElem?_take, if_pos hi]

theorem policyMisses_take (σ : List α) (T : ℕ → Finset α) {r i : ℕ} (hi : i ≤ r) :
    policyMisses (σ.take r) T i = policyMisses σ T i := by
  unfold policyMisses
  congr 1
  apply List.filter_congr
  intro x hx
  rw [List.mem_range] at hx
  exact missB_take σ T (by omega)

theorem legal_take (m : ℕ → ℕ) (σ : List α) (T : ℕ → Finset α) (hT : IsLegal m σ T)
    (r : ℕ) : IsLegal m (σ.take r) T := by
  refine ⟨hT.1, ?_⟩
  intro i hi
  have hi' : i < σ.length := by
    rw [List.length_take] at hi; omega
  have hir : i < r := by
    rw [List.length_take] at hi; omega
  have hget : (σ.take r)[i] = σ[i] := List.getElem_take
  rw [hget, policyMisses_take σ T (le_of_lt hir)]
  exact hT.2 i hi'

theorem seen (m : ℕ → ℕ) (τ : List α) (T : ℕ → Finset α) (hT : IsLegal m τ T) :
    ∀ i ≤ τ.length, ∀ x ∈ T i, x ∈ τ.take i := by
  intro i
  induction i with
  | zero =>
    intro _ x hx
    rw [hT.1] at hx
    simp at hx
  | succ i ih =>
    intro hi x hx
    have hi' : i < τ.length := by omega
    have h1 := (hT.2 i hi').1 hx
    rw [Finset.mem_insert] at h1
    rw [List.take_succ, List.getElem?_eq_getElem hi']
    simp only [List.mem_append, Option.toList_some, List.mem_singleton]
    rcases h1 with h | h
    · exact Or.inr h
    · exact Or.inl (ih (by omega) x h)

theorem cold_miss (m : ℕ → ℕ) (τ : List α) (T : ℕ → Finset α) (hT : IsLegal m τ T)
    (i : ℕ) (hc : IsColdAt τ i) : missB τ T i = true := by
  obtain ⟨hi, hni⟩ := hc
  unfold missB
  rw [List.getElem?_eq_getElem hi]
  simp only [decide_eq_true_eq]
  intro hmem
  exact hni (seen m τ T hT i (le_of_lt hi) _ hmem)

theorem le_policy (m : ℕ → ℕ) (τ : List α) (S T : ℕ → Finset α) (hT : IsLegal m τ T)
    (hcold : AllMissesCold τ S) :
    policyMisses τ S τ.length ≤ policyMisses τ T τ.length := by
  unfold policyMisses
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro x hx hS
  rw [List.mem_range] at hx
  exact cold_miss m τ T hT x (hcold x hx hS)

end Obs31Aux

open Obs31Aux in
theorem solution {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α)
    (S : ℕ → Finset α) (hS : IsLegal m σ S) (hcold : AllMissesCold σ S) :
    ∀ r ≤ σ.length, policyMisses σ S r = optMisses m (σ.take r) := by
  intro r hr
  set τ := σ.take r with hτ
  have hlen : τ.length = r := by
    rw [hτ, List.length_take]; omega
  have hS' : IsLegal m τ S := legal_take m σ S hS r
  have hcold' : AllMissesCold τ S := by
    intro i hi hmiss
    have hir : i < r := by omega
    rw [hτ, missB_take σ S hir] at hmiss
    obtain ⟨hi2, hni⟩ := hcold i (by omega) hmiss
    refine ⟨hi, ?_⟩
    have hget : τ[i] = σ[i] := List.getElem_take
    rw [hget]
    have htt : τ.take i = σ.take i := by
      rw [hτ, List.take_take, Nat.min_eq_left (le_of_lt hir)]
    rw [htt]
    exact hni
  have heq : policyMisses σ S r = policyMisses τ S τ.length := by
    rw [hlen, hτ, policyMisses_take σ S le_rfl]
  rw [heq]
  unfold optMisses
  apply le_antisymm
  · apply le_csInf
    · exact ⟨_, S, hS', rfl⟩
    · rintro k ⟨T, hT, rfl⟩
      exact le_policy m τ S T hT hcold'
  · exact Nat.sInf_le ⟨S, hS', rfl⟩
