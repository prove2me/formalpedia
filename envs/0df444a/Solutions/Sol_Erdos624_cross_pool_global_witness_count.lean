-- Prove2me | solution 1 for Erdos624.cross_pool_global_witness_count
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T20:30:00.016569+00:00
-- url     : https://prove2.me/submissions/96034869-d0a8-4dbb-8b15-7e9396396321

import Mathlib
open Finset

namespace E624R15Q
open Finset

lemma aux_lin (l : ℕ) (hl : 16 ≤ l) : 8 * l + 8 ≤ 2 ^ (l - 1) := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [show m + 1 - 1 = (m - 1) + 1 by omega, pow_succ]
    omega

lemma aux_pow (k : ℕ) (hk : 128 ≤ k) : (256 * k) ^ 4 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ 2 m]
    have h1 : (256 * (m + 1)) ^ 4 ≤ 2 * (256 * m) ^ 4 := by
      have : (m + 1) ^ 4 ≤ 2 * m ^ 4 := by
        have h4 : (m + 1) ^ 4 = m ^ 4 + (4 * m ^ 3 + 6 * m ^ 2 + 4 * m + 1) := by ring
        have : 4 * m ^ 3 + 6 * m ^ 2 + 4 * m + 1 ≤ m ^ 4 := by
          have a1 : 128 * m ^ 3 ≤ m ^ 4 := by
            rw [pow_succ m 3, mul_comm (m ^ 3) m]; exact Nat.mul_le_mul_right _ hm
          have a2 : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
          have a3 : m ≤ m ^ 3 := by
            calc m = m ^ 1 := (pow_one m).symm
              _ ≤ m ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
          have a4 : 1 ≤ m ^ 3 := Nat.one_le_pow _ _ (by omega)
          omega
        omega
      calc (256 * (m + 1)) ^ 4 = 256 ^ 4 * (m + 1) ^ 4 := by ring
        _ ≤ 256 ^ 4 * (2 * m ^ 4) := Nat.mul_le_mul_left _ this
        _ = 2 * (256 * m) ^ 4 := by ring
    omega

theorem short_bound (k : ℕ) (hk : 128 ≤ k) :
    (256 * k) ^ 4 * (2 * ∑ a ∈ Icc 1 (k / (4 * Nat.clog 2 k)), (k ^ 3).choose a) ^ 8 ≤
      2 ^ (8 * k) ∧
    (2 * ∑ a ∈ Icc 1 (k / (4 * Nat.clog 2 k)), (k ^ 3).choose a) ^ 8 ≤ 2 ^ (7 * k) := by
  set l := Nat.clog 2 k with hl
  set R := k / (4 * l) with hR
  have hkl : k ≤ 2 ^ l := Nat.le_pow_clog (by norm_num) k
  have hlt : 2 ^ (l - 1) < k := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := k) (by omega)
    rwa [Nat.pred_eq_sub_one] at this
  have hl8 : 8 * l + 8 ≤ k := by
    by_cases h : l ≤ 15
    · omega
    · have := aux_lin l (by omega); omega
  have hRk : R ≤ k := Nat.div_le_self _ _
  have h4R : 4 * l * R ≤ k := by rw [hR, mul_comm]; exact Nat.div_mul_le_self _ _
  -- crude bound
  have hsum : ∑ a ∈ Icc 1 R, (k ^ 3).choose a ≤ R * (k ^ 3) ^ R := by
    calc ∑ a ∈ Icc 1 R, (k ^ 3).choose a ≤ ∑ _a ∈ Icc 1 R, (k ^ 3) ^ R :=
          sum_le_sum fun a ha => (Nat.choose_le_pow _ _).trans
            (Nat.pow_le_pow_right (by positivity) (mem_Icc.1 ha).2)
      _ = R * (k ^ 3) ^ R := by rw [sum_const, Nat.card_Icc, smul_eq_mul]; congr 1
  have hK : (k ^ 3) ^ R ≤ 2 ^ (3 * l * R) := by
    calc (k ^ 3) ^ R = k ^ (3 * R) := by rw [← pow_mul]
      _ ≤ (2 ^ l) ^ (3 * R) := Nat.pow_le_pow_left hkl _
      _ = 2 ^ (3 * l * R) := by rw [← pow_mul]; congr 1; ring
  have hH : 2 * ∑ a ∈ Icc 1 R, (k ^ 3).choose a ≤ 2 ^ (1 + l + 3 * l * R) := by
    calc 2 * ∑ a ∈ Icc 1 R, (k ^ 3).choose a ≤ 2 * (R * (k ^ 3) ^ R) :=
          Nat.mul_le_mul_left _ hsum
      _ ≤ 2 * (2 ^ l * 2 ^ (3 * l * R)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (hRk.trans hkl) hK)
      _ = 2 ^ (1 + l + 3 * l * R) := by rw [pow_add, pow_add, pow_one]; ring
  have hH8 : (2 * ∑ a ∈ Icc 1 R, (k ^ 3).choose a) ^ 8 ≤ 2 ^ (7 * k) := by
    calc (2 * ∑ a ∈ Icc 1 R, (k ^ 3).choose a) ^ 8 ≤ (2 ^ (1 + l + 3 * l * R)) ^ 8 :=
          Nat.pow_le_pow_left hH 8
      _ = 2 ^ (8 * (1 + l + 3 * l * R)) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (7 * k) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  refine ⟨?_, hH8⟩
  calc (256 * k) ^ 4 * (2 * ∑ a ∈ Icc 1 R, (k ^ 3).choose a) ^ 8 ≤ 2 ^ k * 2 ^ (7 * k) :=
        Nat.mul_le_mul (aux_pow k hk) hH8
    _ = 2 ^ (8 * k) := by rw [← pow_add]; congr 1; ring

theorem global {U : Type*} [DecidableEq U] {C : Type*} [DecidableEq C]
    {ι : Type*} [DecidableEq ι]
    (L : Finset U → Finset C) (hb : ∀ A, #(L A) ≤ 2) (k R s : ℕ) (I : Finset ι)
    (W : ι → Finset U) (hW : ∀ i ∈ I, ∀ h ∈ I, i ≠ h → #(W i ∩ W h) ≤ R)
    (S : ι → Finset C) (G : ι → C → Finset (Finset U)) (a : ι → C → ℕ)
    (hS : ∀ i ∈ I, ∀ u ∈ S i,
      (∀ A ⊆ W i, #A ≤ R → u ∉ L A) ∧
      (∀ P ⊆ W i, #(W i) ≤ #P + s → ∃ Y ⊆ P, #Y = k ∧ ∀ A ⊆ Y, #A = a i u → u ∉ L A) ∧
      G i u ⊆ (W i).powerset ∧ (∀ A ∈ G i u, u ∈ L A) ∧
      (∀ Y ⊆ W i, #Y = k → ∃ A ∈ G i u, A ⊆ Y)) :
    (s + 1) * ∑ i ∈ I, #(S i) ≤
      2 * #(I.biUnion fun i => (S i).biUnion fun u => (G i u).filter (fun A => #A ≠ a i u)) := by
  classical
  set O := fun i u => (G i u).filter (fun A => #A ≠ a i u) with hO
  set Un := I.biUnion fun i => (S i).biUnion fun u => O i u with hUn
  -- (OFF): each off-layer family has at least s+1 members
  have hoff : ∀ i ∈ I, ∀ u ∈ S i, s + 1 ≤ #(O i u) := by
    intro i hi u hu
    obtain ⟨hshort, hM, hGW, hGu, hGcov⟩ := hS i hi u hu
    by_contra hlt
    push_neg at hlt
    have hne : ∀ A : ↥(O i u), ∃ x, x ∈ (A : Finset U) := by
      intro A
      obtain ⟨hAG, -⟩ := mem_filter.1 A.2
      have hAW := mem_powerset.1 (hGW hAG)
      by_contra h
      push_neg at h
      have h0 : (A : Finset U) = ∅ := eq_empty_of_forall_notMem h
      exact hshort _ hAW (by rw [h0]; simp) (hGu _ hAG)
    choose pt hpt using hne
    set D := (univ : Finset ↥(O i u)).image pt with hD
    have hDc : #D ≤ s := card_image_le.trans (by rw [card_univ, Fintype.card_coe]; omega)
    have hPc : #(W i) ≤ #(W i \ D) + s := by
      have := le_card_sdiff D (W i); omega
    obtain ⟨Y, hYP, hYk, hY⟩ := hM (W i \ D) sdiff_subset hPc
    obtain ⟨A, hAG, hAY⟩ := hGcov Y (hYP.trans sdiff_subset) hYk
    by_cases hAa : #A = a i u
    · exact hY A hAY hAa (hGu A hAG)
    · have hAO : A ∈ O i u := mem_filter.2 ⟨hAG, hAa⟩
      have h1 := hYP (hAY (hpt ⟨A, hAO⟩))
      exact (mem_sdiff.1 h1).2 (mem_image_of_mem pt (mem_univ _))
  -- each input of the union is counted at most twice
  have hA2 : ∀ A ∈ Un, ∑ i ∈ I, #((S i).filter (fun u => A ∈ O i u)) ≤ 2 := by
    intro A _
    set J := I.filter (fun i => ((S i).filter (fun u => A ∈ O i u)).Nonempty) with hJ
    have hJ1 : #J ≤ 1 := by
      rw [card_le_one]
      intro i hi h hh
      by_contra hne
      obtain ⟨hiI, u, hu⟩ := mem_filter.1 hi
      obtain ⟨hhI, v, hv⟩ := mem_filter.1 hh
      obtain ⟨huS, huA⟩ := mem_filter.1 hu
      obtain ⟨hvS, hvA⟩ := mem_filter.1 hv
      have hAi := mem_powerset.1 ((hS i hiI u huS).2.2.1 (mem_filter.1 huA).1)
      have hAh := mem_powerset.1 ((hS h hhI v hvS).2.2.1 (mem_filter.1 hvA).1)
      have hc := (card_le_card (subset_inter hAi hAh)).trans (hW i hiI h hhI hne)
      exact (hS i hiI u huS).1 A hAi hc ((hS i hiI u huS).2.2.2.1 A (mem_filter.1 huA).1)
    rw [← sum_filter_of_ne (p := fun i => ((S i).filter (fun u => A ∈ O i u)).Nonempty)
      (fun i _ h => by rwa [← card_pos, Nat.pos_iff_ne_zero])]
    calc ∑ i ∈ J, #((S i).filter (fun u => A ∈ O i u)) ≤ ∑ _i ∈ J, 2 := by
          refine sum_le_sum fun i hi => ?_
          obtain ⟨hiI, -⟩ := mem_filter.1 hi
          refine (card_le_card fun u hu => ?_).trans (hb A)
          obtain ⟨huS, huA⟩ := mem_filter.1 hu
          exact (hS i hiI u huS).2.2.2.1 A (mem_filter.1 huA).1
      _ = #J * 2 := by rw [sum_const, smul_eq_mul]
      _ ≤ 2 := by omega
  have hswap : ∑ i ∈ I, ∑ u ∈ S i, #(O i u) =
      ∑ A ∈ Un, ∑ i ∈ I, #((S i).filter (fun u => A ∈ O i u)) := by
    have e : ∀ i ∈ I, ∀ u ∈ S i, #(O i u) = ∑ A ∈ Un, if A ∈ O i u then 1 else 0 := by
      intro i hi u hu
      rw [← card_filter]
      congr 1; ext A; simp only [mem_filter]
      constructor
      · intro h; refine ⟨?_, h⟩
        rw [hUn, mem_biUnion]; exact ⟨i, hi, mem_biUnion.2 ⟨u, hu, h⟩⟩
      · exact fun h => h.2
    rw [sum_congr rfl fun i hi => sum_congr rfl fun u hu => e i hi u hu]
    have e2 : ∀ i, ∑ u ∈ S i, ∑ A ∈ Un, (if A ∈ O i u then 1 else 0) =
        ∑ A ∈ Un, #((S i).filter (fun u => A ∈ O i u)) := fun i => by
      rw [sum_comm]; simp only [card_filter]
    rw [sum_congr rfl fun i _ => e2 i, sum_comm]
  calc (s + 1) * ∑ i ∈ I, #(S i) = ∑ i ∈ I, ∑ _u ∈ S i, (s + 1) := by
        rw [mul_sum]; refine sum_congr rfl fun i _ => ?_; rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ I, ∑ u ∈ S i, #(O i u) :=
        sum_le_sum fun i hi => sum_le_sum fun u hu => hoff i hi u hu
    _ = ∑ A ∈ Un, ∑ i ∈ I, #((S i).filter (fun u => A ∈ O i u)) := hswap
    _ ≤ ∑ _A ∈ Un, 2 := sum_le_sum hA2
    _ = 2 * #Un := by rw [sum_const, smul_eq_mul, mul_comm]
end E624R15Q

namespace Erdos624

theorem cross_pool_global_witness_count {U : Type*} [DecidableEq U] {C : Type*} [DecidableEq C]
    {ι : Type*} [DecidableEq ι]
    (L : Finset U → Finset C) (hb : ∀ A, #(L A) ≤ 2) (k R s : ℕ) (I : Finset ι)
    (W : ι → Finset U) (hW : ∀ i ∈ I, ∀ h ∈ I, i ≠ h → #(W i ∩ W h) ≤ R)
    (S : ι → Finset C) (G : ι → C → Finset (Finset U)) (a : ι → C → ℕ)
    (hS : ∀ i ∈ I, ∀ u ∈ S i,
      (∀ A ⊆ W i, #A ≤ R → u ∉ L A) ∧
      (∀ P ⊆ W i, #(W i) ≤ #P + s → ∃ Y ⊆ P, #Y = k ∧ ∀ A ⊆ Y, #A = a i u → u ∉ L A) ∧
      G i u ⊆ (W i).powerset ∧ (∀ A ∈ G i u, u ∈ L A) ∧
      (∀ Y ⊆ W i, #Y = k → ∃ A ∈ G i u, A ⊆ Y)) :
    (s + 1) * ∑ i ∈ I, #(S i) ≤
      2 * #(I.biUnion fun i => (S i).biUnion fun u => (G i u).filter (fun A => #A ≠ a i u)) := by
  exact E624R15Q.global L hb k R s I W hW S G a hS

end Erdos624

open Finset

theorem solution {U : Type*} [DecidableEq U] {C : Type*} [DecidableEq C]
    {ι : Type*} [DecidableEq ι]
    (L : Finset U → Finset C) (hb : ∀ A, #(L A) ≤ 2) (k R s : ℕ) (I : Finset ι)
    (W : ι → Finset U) (hW : ∀ i ∈ I, ∀ h ∈ I, i ≠ h → #(W i ∩ W h) ≤ R)
    (S : ι → Finset C) (G : ι → C → Finset (Finset U)) (a : ι → C → ℕ)
    (hS : ∀ i ∈ I, ∀ u ∈ S i,
      (∀ A ⊆ W i, #A ≤ R → u ∉ L A) ∧
      (∀ P ⊆ W i, #(W i) ≤ #P + s → ∃ Y ⊆ P, #Y = k ∧ ∀ A ⊆ Y, #A = a i u → u ∉ L A) ∧
      G i u ⊆ (W i).powerset ∧ (∀ A ∈ G i u, u ∈ L A) ∧
      (∀ Y ⊆ W i, #Y = k → ∃ A ∈ G i u, A ⊆ Y)) :
    (s + 1) * ∑ i ∈ I, #(S i) ≤
      2 * #(I.biUnion fun i => (S i).biUnion fun u => (G i u).filter (fun A => #A ≠ a i u)) :=
  Erdos624.cross_pool_global_witness_count L hb k R s I W hW S G a hS
