-- Prove2me | solution 1 for BeyondGomoryHu.Units.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:34:21.774943+00:00
-- url     : https://prove2.me/submissions/08d7fb9e-1e35-4245-bbae-5a8278403b1b

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]

private lemma cap_eq_sum (G : WGraph V) (C : Finset V) :
    cap G C = ∑ a : V, ∑ b : V, if a ∈ C ∧ b ∉ C then G.w a b else 0 := by
  classical
  symm
  rw [← Finset.sum_subset (Finset.subset_univ C) (by
    intro a ha haC
    simp [haC])]
  simp only [cap]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [ha, true_and]
  symm
  calc
    (∑ b ∈ Cᶜ, G.w a b) = ∑ b ∈ Cᶜ, (if b ∉ C then G.w a b else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      simp at hb
      simp [hb]
    _ = ∑ b : V, (if b ∉ C then G.w a b else 0) := by
      apply Finset.sum_subset (Finset.subset_univ Cᶜ)
      intro b hb hbC
      simp only [Finset.mem_compl, not_not] at hbC
      simp [hbC]

private lemma cap_compl (G : WGraph V) (A : Finset V) : cap G Aᶜ = cap G A := by
  classical
  simp only [cap, compl_compl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact G.symm _ _

private lemma cap_submod (G : WGraph V) (A B : Finset V) :
    cap G (A ∩ B) + cap G (A ∪ B) ≤ cap G A + cap G B := by
  classical
  rw [cap_eq_sum, cap_eq_sum, cap_eq_sum, cap_eq_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b hb
  simp only [Finset.mem_inter, Finset.mem_union]
  by_cases haA : a ∈ A <;> by_cases haB : a ∈ B <;>
    by_cases hbA : b ∈ A <;> by_cases hbB : b ∈ B <;>
    simp [haA, haB, hbA, hbB]

private lemma cap_posimod (G : WGraph V) (A B : Finset V) :
    cap G (A \ B) + cap G (B \ A) ≤ cap G A + cap G B := by
  classical
  have h := cap_submod G Aᶜ B
  have h₁ : Aᶜ ∩ B = B \ A := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff]
    tauto
  have h₂ : (Aᶜ ∪ B)ᶜ = A \ B := by ext x; simp
  rw [h₁, ← cap_compl G (Aᶜ ∪ B), h₂, cap_compl G A] at h
  omega

private lemma cap_four (G : WGraph V) (A B : Finset V) :
    cap G (A ∩ B) + cap G (A ∪ B) + cap G (A \ B) + cap G (B \ A) ≤
      2 * cap G A + 2 * cap G B := by
  have hsub := cap_submod G A B
  have hpos := cap_posimod G A B
  omega

private lemma mincuts_of_pair {G : WGraph V} {S T A B X Y : Finset V}
    (hA : IsMincut G S A) (hB : IsMincut G T B)
    (hX : IsCut S X) (hY : IsCut T Y)
    (hcap : cap G X + cap G Y ≤ cap G A + cap G B) :
    IsMincut G S X ∧ IsMincut G T Y := by
  constructor
  · refine ⟨hX, fun C hC => ?_⟩
    have hAC := hA.2 C hC
    have hBY := hB.2 Y hY
    omega
  · refine ⟨hY, fun C hC => ?_⟩
    have hAX := hA.2 X hX
    have hBC := hB.2 C hC
    omega

private lemma isCut_of_mem {V : Type} [DecidableEq V] {S X : Finset V} {x y : V}
    (hxS : x ∈ S) (hxX : x ∈ X) (hyS : y ∈ S) (hyX : y ∉ X) : IsCut S X := by
  exact ⟨⟨x, Finset.mem_inter.mpr ⟨hxX, hxS⟩⟩,
    ⟨y, Finset.mem_sdiff.mpr ⟨hyS, hyX⟩⟩⟩

end BeyondGomoryHu.Units

open BeyondGomoryHu.Units

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (S T A B : Finset V)
    (hA : IsMincut G S A) (hB : IsMincut G T B) :
    ((IsCut S (A ∩ B) ∧ IsCut T (A ∪ B) → IsMincut G S (A ∩ B) ∧ IsMincut G T (A ∪ B)) ∧
     (IsCut S (A ∪ B) ∧ IsCut T (A ∩ B) → IsMincut G S (A ∪ B) ∧ IsMincut G T (A ∩ B))) ∧
    ((IsCut S (A \ B) ∧ IsCut T (B \ A) → IsMincut G S (A \ B) ∧ IsMincut G T (B \ A)) ∧
     (IsCut S (B \ A) ∧ IsCut T (A \ B) → IsMincut G S (B \ A) ∧ IsMincut G T (A \ B))) ∧
    (∀ i j : Fin 4, i ≠ j → IsCut S (fourCuts A B i) → IsCut S (fourCuts A B j) →
      (∀ l : Fin 4, l ≠ i → l ≠ j → IsCut T (fourCuts A B l)) →
      IsMincut G S (fourCuts A B i) ∧ IsMincut G S (fourCuts A B j) ∧
        ∀ l : Fin 4, l ≠ i → l ≠ j → IsMincut G T (fourCuts A B l)) ∧
    ((IsCut S (A ∩ B) ∧ IsCut T (A ∪ B)) ∨ (IsCut S (A ∪ B) ∧ IsCut T (A ∩ B)) ∨
     (IsCut S (A \ B) ∧ IsCut T (B \ A)) ∨ (IsCut S (B \ A) ∧ IsCut T (A \ B)) ∨
     (∃ i j : Fin 4, i ≠ j ∧ IsCut S (fourCuts A B i) ∧ IsCut S (fourCuts A B j) ∧
       ∀ l : Fin 4, l ≠ i → l ≠ j → IsCut T (fourCuts A B l))) := by
  classical
  have hsub := BeyondGomoryHu.Units.cap_submod G A B
  have hpos := BeyondGomoryHu.Units.cap_posimod G A B
  have hfour := BeyondGomoryHu.Units.cap_four G A B
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨hS, hT⟩
    exact BeyondGomoryHu.Units.mincuts_of_pair hA hB hS hT hsub
  · rintro ⟨hS, hT⟩
    exact BeyondGomoryHu.Units.mincuts_of_pair hA hB hS hT (by omega)
  · rintro ⟨hS, hT⟩
    exact BeyondGomoryHu.Units.mincuts_of_pair hA hB hS hT hpos
  · rintro ⟨hS, hT⟩
    exact BeyondGomoryHu.Units.mincuts_of_pair hA hB hS hT (by omega)
  · intro i j hij hsi hsj hrest
    fin_cases i <;> fin_cases j <;>
      simp_all [fourCuts, Fin.forall_fin_succ, IsMincut] <;> grind
  · rcases hA.1.1 with ⟨s₁, hs₁⟩
    rcases hA.1.2 with ⟨s₂, hs₂⟩
    rcases hB.1.1 with ⟨t₁, ht₁⟩
    rcases hB.1.2 with ⟨t₂, ht₂⟩
    simp only [Finset.mem_inter] at hs₁ ht₁
    simp only [Finset.mem_sdiff] at hs₂ ht₂
    have hIS (h : s₁ ∈ B) : IsCut S (A ∩ B) :=
      BeyondGomoryHu.Units.isCut_of_mem hs₁.2 (by simp [hs₁.1, h]) hs₂.1 (by simp [hs₂.2])
    have hUS (h : s₂ ∉ B) : IsCut S (A ∪ B) :=
      BeyondGomoryHu.Units.isCut_of_mem hs₁.2 (by simp [hs₁.1]) hs₂.1 (by simp [hs₂.2, h])
    have hYS (h : s₁ ∉ B) : IsCut S (A \ B) :=
      BeyondGomoryHu.Units.isCut_of_mem hs₁.2 (by simp [hs₁.1, h]) hs₂.1 (by simp [hs₂.2])
    have hZS (h : s₂ ∈ B) : IsCut S (B \ A) :=
      BeyondGomoryHu.Units.isCut_of_mem hs₂.1 (by simp [h, hs₂.2]) hs₁.2 (by simp [hs₁.1])
    have hIT (h : t₁ ∈ A) : IsCut T (A ∩ B) :=
      BeyondGomoryHu.Units.isCut_of_mem ht₁.2 (by simp [h, ht₁.1]) ht₂.1 (by simp [ht₂.2])
    have hUT (h : t₂ ∉ A) : IsCut T (A ∪ B) :=
      BeyondGomoryHu.Units.isCut_of_mem ht₁.2 (by simp [ht₁.1]) ht₂.1 (by simp [h, ht₂.2])
    have hYT (h : t₂ ∈ A) : IsCut T (A \ B) :=
      BeyondGomoryHu.Units.isCut_of_mem ht₂.1 (by simp [h, ht₂.2]) ht₁.2 (by simp [ht₁.1])
    have hZT (h : t₁ ∉ A) : IsCut T (B \ A) :=
      BeyondGomoryHu.Units.isCut_of_mem ht₁.2 (by simp [h, ht₁.1]) ht₂.1 (by simp [ht₂.2])
    by_cases hs₁B : s₁ ∈ B <;> by_cases hs₂B : s₂ ∈ B <;>
      by_cases ht₁A : t₁ ∈ A <;> by_cases ht₂A : t₂ ∈ A
    all_goals
      first
      | exact Or.inl ⟨hIS hs₁B, hUT ht₂A⟩
      | exact Or.inr (Or.inl ⟨hUS hs₂B, hIT ht₁A⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨hYS hs₁B, hZT ht₁A⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hZS hs₂B, hYT ht₂A⟩)))
      | (right; right; right; right;
         refine ⟨0, 1, by decide, hIS hs₁B, hUS hs₂B, ?_⟩
         intro l hl₀ hl₁
         fin_cases l <;> simp_all [fourCuts, hYT ht₂A, hZT ht₁A])
      | (right; right; right; right;
         refine ⟨2, 3, by decide, hYS hs₁B, hZS hs₂B, ?_⟩
         intro l hl₂ hl₃
         fin_cases l <;> simp_all [fourCuts, hIT ht₁A, hUT ht₂A])
