-- Prove2me | solution 1 for Erdos624.lower_layer_occurrence_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:36:47.752131+00:00
-- url     : https://prove2.me/submissions/c9713f56-2d1a-4a66-8755-160f8414c0f7

import Mathlib
open Finset

namespace E624R14L
open Finset

lemma card_filter_powerset_Icc {U : Type*} [DecidableEq U] (Z : Finset U) (lo hi : ℕ) :
    #(Z.powerset.filter (fun A => lo ≤ #A ∧ #A ≤ hi)) = ∑ a ∈ Icc lo hi, (#Z).choose a := by
  have : Z.powerset.filter (fun A => lo ≤ #A ∧ #A ≤ hi) =
      (Icc lo hi).biUnion (fun a => Z.powersetCard a) := by
    ext A
    simp only [mem_filter, mem_powerset, mem_biUnion, mem_Icc, mem_powersetCard]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨#A, ⟨h2, h3⟩, h1, rfl⟩
    · rintro ⟨a, ⟨h2, h3⟩, h1, rfl⟩; exact ⟨h1, h2, h3⟩
  rw [this, card_biUnion]
  · exact sum_congr rfl fun a _ => card_powersetCard a Z
  · intro a _ c _ hac
    rw [Function.onFun, disjoint_left]
    intro A hA hA'
    rw [mem_powersetCard] at hA hA'
    exact hac (hA.2.symm.trans hA'.2)

theorem layer {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (b k h : ℕ) (hb : ∀ A, #(L A) ≤ b) (hh : 1 ≤ h)
    (Z : Finset U) (hZ : #Z = k + 1)
    (hcov : ∀ x ∈ Z, ∀ u : C, ∃ A ⊆ Z.erase x, u ∈ L A) :
    3 * (Fintype.card C - #((Z.powerset.filter (fun A => #A < h)).biUnion L)) ≤
      b * (∑ a ∈ Icc h k, (k + 1).choose a + ∑ a ∈ Icc h ((k + 1) / 2), (k + 1).choose a) := by
  classical
  set P := (Z.powerset.filter (fun A => #A < h)).biUnion L with hP
  set M := (univ : Finset C).filter (fun u => u ∉ P) with hM
  have hMcard : #M = Fintype.card C - #P := by
    rw [hM, filter_not, card_sdiff_of_subset (by simp), card_univ]
    simp
  set Lay := Z.powerset.filter (fun A => h ≤ #A ∧ #A ≤ k) with hLay
  set Sm := Z.powerset.filter (fun A => h ≤ #A ∧ #A ≤ (k + 1) / 2) with hSm
  have hLayc : #Lay = ∑ a ∈ Icc h k, (k + 1).choose a := by
    rw [hLay, card_filter_powerset_Icc, hZ]
  have hSmc : #Sm = ∑ a ∈ Icc h ((k + 1) / 2), (k + 1).choose a := by
    rw [hSm, card_filter_powerset_Icc, hZ]
  set occ := fun u => Lay.filter (fun A => u ∈ L A) with hocc
  -- witnesses of colours in M lie in the layer range
  have hin : ∀ u ∈ M, ∀ A ⊆ Z, #A ≤ k → u ∈ L A → A ∈ occ u := by
    intro u hu A hAZ hAk huA
    rw [hM, mem_filter] at hu
    have : h ≤ #A := by
      by_contra hc
      apply hu.2
      rw [hP, mem_biUnion]
      exact ⟨A, mem_filter.2 ⟨mem_powerset.2 hAZ, by omega⟩, huA⟩
    simp only [hocc, hLay, mem_filter, mem_powerset]
    exact ⟨⟨hAZ, this, hAk⟩, huA⟩
  have hface : ∀ u ∈ M, ∀ x ∈ Z, ∃ A ∈ occ u, x ∉ A := by
    intro u hu x hx
    obtain ⟨A, hAZ, huA⟩ := hcov x hx u
    have hAk : #A ≤ k := by
      have := card_le_card hAZ; rw [card_erase_of_mem hx, hZ] at this; omega
    exact ⟨A, hin u hu A (hAZ.trans (erase_subset _ _)) hAk huA,
      fun h' => by have := hAZ h'; simp at this⟩
  have hocc_sub : ∀ u, ∀ A ∈ occ u, A ⊆ Z ∧ h ≤ #A := by
    intro u A hA
    simp only [hocc, hLay, mem_filter, mem_powerset] at hA
    exact ⟨hA.1.1, hA.1.2.1⟩
  have hkey : ∀ u ∈ M, 3 ≤ #(occ u) + (if ∃ A ∈ Sm, u ∈ L A then 1 else 0) := by
    intro u hu
    obtain ⟨x, hx⟩ : Z.Nonempty := card_pos.1 (by omega)
    obtain ⟨A1, hA1, hxA1⟩ := hface u hu x hx
    obtain ⟨y, hy⟩ : A1.Nonempty := card_pos.1 (by have := (hocc_sub u A1 hA1).2; omega)
    obtain ⟨A2, hA2, hyA2⟩ := hface u hu y ((hocc_sub u A1 hA1).1 hy)
    have h12 : A1 ≠ A2 := fun e => hyA2 (e ▸ hy)
    by_cases hdis : Disjoint A1 A2
    · have hsz : #A1 + #A2 ≤ k + 1 := by
        rw [← card_union_of_disjoint hdis, ← hZ]
        exact card_le_card (union_subset (hocc_sub u A1 hA1).1 (hocc_sub u A2 hA2).1)
      have hsmall : ∃ A ∈ Sm, u ∈ L A := by
        by_cases hc : #A1 ≤ (k + 1) / 2
        · refine ⟨A1, ?_, (mem_filter.1 hA1).2⟩
          simp only [hSm, mem_filter, mem_powerset]
          exact ⟨(hocc_sub u A1 hA1).1, (hocc_sub u A1 hA1).2, hc⟩
        · refine ⟨A2, ?_, (mem_filter.1 hA2).2⟩
          simp only [hSm, mem_filter, mem_powerset]
          exact ⟨(hocc_sub u A2 hA2).1, (hocc_sub u A2 hA2).2, by omega⟩
      rw [if_pos hsmall]
      have : 2 ≤ #(occ u) := by
        have : ({A1, A2} : Finset (Finset U)) ⊆ occ u := by
          intro A hA; rw [mem_insert, mem_singleton] at hA
          rcases hA with rfl | rfl <;> assumption
        have := card_le_card this; rw [card_pair h12] at this; exact this
      omega
    · rw [not_disjoint_iff] at hdis
      obtain ⟨z, hz1, hz2⟩ := hdis
      obtain ⟨A3, hA3, hzA3⟩ := hface u hu z ((hocc_sub u A1 hA1).1 hz1)
      have h13 : A1 ≠ A3 := fun e => hzA3 (e ▸ hz1)
      have h23 : A2 ≠ A3 := fun e => hzA3 (e ▸ hz2)
      have : ({A1, A2, A3} : Finset (Finset U)) ⊆ occ u := by
        intro A hA; simp only [mem_insert, mem_singleton] at hA
        rcases hA with rfl | rfl | rfl <;> assumption
      have := card_le_card this
      rw [card_insert_of_notMem (by simp [h12, h13]), card_pair h23] at this
      omega
  -- capacity counts
  have hsumocc : ∑ u ∈ M, #(occ u) ≤ b * #Lay := by
    have h1 : ∑ u ∈ M, #(occ u) = ∑ A ∈ Lay, #(M.filter (fun u => u ∈ L A)) := by
      simp only [hocc, card_filter]
      exact sum_comm
    rw [h1]
    calc ∑ A ∈ Lay, #(M.filter (fun u => u ∈ L A)) ≤ ∑ A ∈ Lay, #(L A) :=
          sum_le_sum fun A _ => card_le_card fun u hu => (mem_filter.1 hu).2
      _ ≤ ∑ _A ∈ Lay, b := sum_le_sum fun A _ => hb A
      _ = b * #Lay := by rw [sum_const, smul_eq_mul, mul_comm]
  have hsmallcnt : ∑ u ∈ M, (if ∃ A ∈ Sm, u ∈ L A then 1 else 0) ≤ b * #Sm := by
    rw [← card_filter]
    calc #(M.filter (fun u => ∃ A ∈ Sm, u ∈ L A)) ≤ #(Sm.biUnion L) := by
          apply card_le_card
          intro u hu
          obtain ⟨A, hA, huA⟩ := (mem_filter.1 hu).2
          exact mem_biUnion.2 ⟨A, hA, huA⟩
      _ ≤ ∑ A ∈ Sm, #(L A) := card_biUnion_le
      _ ≤ ∑ _A ∈ Sm, b := sum_le_sum fun A _ => hb A
      _ = b * #Sm := by rw [sum_const, smul_eq_mul, mul_comm]
  have hlow : ∑ _u ∈ M, 3 ≤ ∑ u ∈ M, (#(occ u) + (if ∃ A ∈ Sm, u ∈ L A then 1 else 0)) :=
    sum_le_sum hkey
  rw [sum_const, smul_eq_mul, sum_add_distrib] at hlow
  rw [← hMcard, ← hLayc, ← hSmc]
  nlinarith
end E624R14L

namespace Erdos624

theorem lower_layer_occurrence_inequality {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (b k h : ℕ) (hb : ∀ A, #(L A) ≤ b) (hh : 1 ≤ h)
    (Z : Finset U) (hZ : #Z = k + 1)
    (hcov : ∀ x ∈ Z, ∀ u : C, ∃ A ⊆ Z.erase x, u ∈ L A) :
    3 * (Fintype.card C - #((Z.powerset.filter (fun A => #A < h)).biUnion L)) ≤
      b * (∑ a ∈ Icc h k, (k + 1).choose a + ∑ a ∈ Icc h ((k + 1) / 2), (k + 1).choose a) := by
  exact E624R14L.layer L b k h hb hh Z hZ hcov

end Erdos624

open Finset

theorem solution {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (b k h : ℕ) (hb : ∀ A, #(L A) ≤ b) (hh : 1 ≤ h)
    (Z : Finset U) (hZ : #Z = k + 1)
    (hcov : ∀ x ∈ Z, ∀ u : C, ∃ A ⊆ Z.erase x, u ∈ L A) :
    3 * (Fintype.card C - #((Z.powerset.filter (fun A => #A < h)).biUnion L)) ≤
      b * (∑ a ∈ Icc h k, (k + 1).choose a + ∑ a ∈ Icc h ((k + 1) / 2), (k + 1).choose a) :=
  Erdos624.lower_layer_occurrence_inequality L b k h hb hh Z hZ hcov
