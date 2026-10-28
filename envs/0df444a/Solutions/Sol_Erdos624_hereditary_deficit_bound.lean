-- Prove2me | solution 1 for Erdos624.hereditary_deficit_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T20:10:41.836737+00:00
-- url     : https://prove2.me/submissions/24392f36-49a6-4cfe-980f-555ae98def37

import Mathlib
open Finset

namespace E624R15H
open Finset

lemma offdiag_split {U : Type*} [DecidableEq U] (E : Finset U) (f : U × U → ℕ) :
    ∑ q ∈ E ×ˢ E, f q = ∑ q ∈ E.offDiag, f q + ∑ i ∈ E, f (i, i) := by
  rw [← diag_union_offDiag, sum_union (disjoint_diag_offDiag E), add_comm]
  congr 1
  refine sum_nbij' (fun q => q.1) (fun i => (i, i)) ?_ ?_ ?_ ?_ ?_
  · intro q hq; simp only [mem_coe, mem_diag] at hq ⊢; exact hq.1
  · intro i hi; simpa using hi
  · intro q hq; simp only [mem_coe, mem_diag] at hq; ext <;> simp [hq.2]
  · intro i _; rfl
  · intro q hq; simp only [mem_coe, mem_diag] at hq
    obtain ⟨a, b⟩ := q; simp only at hq ⊢; rw [hq.2]

lemma cap_pow {U : Type*} [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (hb : ∀ A, #(L A) ≤ 2) (B : Finset U)
    (g : Finset U → Finset U) : #(B.powerset.biUnion (fun A => L (g A))) ≤ 2 * 2 ^ #B := by
  calc _ ≤ ∑ A ∈ B.powerset, #(L (g A)) := card_biUnion_le
    _ ≤ ∑ _A ∈ B.powerset, 2 := sum_le_sum fun A _ => hb _
    _ = 2 * 2 ^ #B := by rw [sum_const, card_powerset, smul_eq_mul, mul_comm]

lemma perB {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (hk : 3 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (hb : ∀ A, #(L A) ≤ 2) (B E : Finset U) (hB : #B = k - 3) (hBE : Disjoint B E) :
    #E ^ 2 * 2 ^ (k - 2) ≤ 3 * ∑ q ∈ E.offDiag,
      (2 ^ k - #((insert q.1 (insert q.2 B)).powerset.biUnion L)) + 3 * #E * 2 ^ (k - 2) := by
  classical
  set p := 2 ^ (k - 2) with hp
  have hn : 2 ^ k = 4 * p := by
    rw [hp, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have h2B : 2 * 2 ^ #B = p := by
    rw [hB, hp, ← pow_succ']; congr 1; omega
  have hpos : 0 < p := by positivity
  set P0 := B.powerset.biUnion L with hP0
  have hP0c : #P0 ≤ p := by
    have := cap_pow L hb B id; simp only [id] at this; rw [h2B] at this; exact this
  set Pi := fun i => B.powerset.biUnion (fun A => L (insert i A)) with hPi
  have hPic : ∀ i, #(Pi i) ≤ p := fun i => (cap_pow L hb B (insert i)).trans h2B.le
  set Pij := fun i j => B.powerset.biUnion (fun A => L (insert i (insert j A))) with hPij
  have hPijc : ∀ i j, #(Pij i j) ≤ p :=
    fun i j => (cap_pow L hb B (fun A => insert i (insert j A))).trans h2B.le
  obtain ⟨P0s, hP0s1, -, hP0sc⟩ := exists_subsuperset_card_eq (subset_univ P0) hP0c
    (by rw [card_univ, hC, hn]; omega)
  set R := (univ : Finset C) \ P0s with hR
  have hRc : #R = 3 * p := by
    rw [hR, card_sdiff_of_subset (subset_univ _), card_univ, hC, hP0sc, hn]; omega
  have hT : ∀ i, ∃ T, Pi i \ P0s ⊆ T ∧ T ⊆ R ∧ #T = p := fun i =>
    exists_subsuperset_card_eq (sdiff_subset_sdiff (subset_univ _) (subset_refl _))
      ((card_le_card sdiff_subset).trans (hPic i)) (by omega)
  choose T hT1 hT2 hT3 using hT
  -- coverage of a face by the four palettes
  have hcover : ∀ i j, i ∉ B → j ∉ B → i ≠ j →
      (insert i (insert j B)).powerset.biUnion L ⊆ P0s ∪ (T i ∪ T j) ∪ Pij i j := by
    intro i j hiB hjB hij c hc
    obtain ⟨A, hA, hcA⟩ := mem_biUnion.1 hc
    rw [mem_powerset] at hA
    set A' := (A.erase i).erase j with hA'
    have hA'B : A' ⊆ B := by
      intro x hx
      simp only [hA', mem_erase] at hx
      have := hA hx.2.2
      simp only [mem_insert] at this
      rcases this with h | h | h
      · exact absurd h hx.2.1
      · exact absurd h hx.1
      · exact h
    have hA'pow : A' ∈ B.powerset := mem_powerset.2 hA'B
    simp only [mem_union]
    by_cases hi : i ∈ A <;> by_cases hj : j ∈ A
    · right
      have e : insert i (insert j A') = A := by
        rw [hA', insert_erase (mem_erase.2 ⟨Ne.symm hij, hj⟩), insert_erase hi]
      exact mem_biUnion.2 ⟨A', hA'pow, e ▸ hcA⟩
    · have e : insert i A' = A := by
        rw [hA', erase_eq_of_notMem (fun h => hj (mem_of_mem_erase h)), insert_erase hi]
      have hc' : c ∈ Pi i := mem_biUnion.2 ⟨A', hA'pow, e ▸ hcA⟩
      by_cases h0 : c ∈ P0s
      · exact Or.inl (Or.inl h0)
      · exact Or.inl (Or.inr (Or.inl (hT1 i (mem_sdiff.2 ⟨hc', h0⟩))))
    · have e : insert j A' = A := by
        rw [hA', erase_eq_of_notMem hi, insert_erase hj]
      have hc' : c ∈ Pi j := mem_biUnion.2 ⟨A', hA'pow, e ▸ hcA⟩
      by_cases h0 : c ∈ P0s
      · exact Or.inl (Or.inl h0)
      · exact Or.inl (Or.inr (Or.inr (hT1 j (mem_sdiff.2 ⟨hc', h0⟩))))
    · have e : A' = A := by rw [hA', erase_eq_of_notMem hi, erase_eq_of_notMem hj]
      exact Or.inl (Or.inl (hP0s1 (mem_biUnion.2 ⟨A', hA'pow, e ▸ hcA⟩)))
  have hD : ∀ q ∈ E.offDiag, #(T q.1 ∩ T q.2) ≤
      2 ^ k - #((insert q.1 (insert q.2 B)).powerset.biUnion L) := by
    intro q hq
    rw [mem_offDiag] at hq
    have hiB : q.1 ∉ B := fun h => disjoint_left.1 hBE h hq.1
    have hjB : q.2 ∉ B := fun h => disjoint_left.1 hBE h hq.2.1
    have h1 := card_le_card (hcover q.1 q.2 hiB hjB hq.2.2)
    have h2 := card_union_le (P0s ∪ (T q.1 ∪ T q.2)) (Pij q.1 q.2)
    have h3 := card_union_le P0s (T q.1 ∪ T q.2)
    have h4 := card_union_add_card_inter (T q.1) (T q.2)
    have h5 := hPijc q.1 q.2
    rw [hT3, hT3] at h4
    omega
  -- double counting on R
  set t := fun c => #(E.filter (fun i => c ∈ T i)) with ht
  have hinter : ∀ i j, #(T i ∩ T j) =
      ∑ c ∈ R, (if c ∈ T i then 1 else 0) * (if c ∈ T j then 1 else 0) := by
    intro i j
    have : T i ∩ T j = R.filter (fun c => c ∈ T i ∧ c ∈ T j) := by
      ext c; simp only [mem_inter, mem_filter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨hT2 i h1, h1, h2⟩
      · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    rw [this, card_filter]
    refine sum_congr rfl fun c _ => ?_
    split_ifs <;> simp_all
  have hprod : ∑ q ∈ E ×ˢ E, #(T q.1 ∩ T q.2) = ∑ c ∈ R, t c ^ 2 := by
    simp_rw [hinter]
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    rw [sum_product]; simp only
    rw [ht]; simp only; rw [sq, card_filter, sum_mul_sum]
  have hlin : ∑ c ∈ R, t c = #E * p := by
    have : ∑ c ∈ R, t c = ∑ i ∈ E, #(T i) := by
      simp only [ht, card_filter]
      rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      rw [← card_filter]
      congr 1; ext c; simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hT2 i h, h⟩⟩
    rw [this, sum_congr rfl fun i _ => hT3 i, sum_const, smul_eq_mul]
  have hdiag : ∑ i ∈ E, #(T (i, i).1 ∩ T (i, i).2) = #E * p := by
    simp only [inter_self]; rw [sum_congr rfl fun i _ => hT3 i, sum_const, smul_eq_mul]
  have hsplit := offdiag_split E (fun q => #(T q.1 ∩ T q.2))
  simp only at hsplit
  rw [hprod] at hsplit
  have hCS := sq_sum_le_card_mul_sum_sq (s := R) (f := t)
  rw [hlin, hRc] at hCS
  have hCS' : #E ^ 2 * p ≤ 3 * ∑ c ∈ R, t c ^ 2 := by
    have : (#E ^ 2 * p) * p ≤ (3 * ∑ c ∈ R, t c ^ 2) * p := by
      calc (#E ^ 2 * p) * p = (#E * p) ^ 2 := by ring
        _ ≤ 3 * p * ∑ c ∈ R, t c ^ 2 := hCS
        _ = (3 * ∑ c ∈ R, t c ^ 2) * p := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have hDsum := sum_le_sum hD
  have hd2 : ∑ i ∈ E, #(T i ∩ T i) = #E * p := by
    simp only [inter_self]; rw [sum_congr rfl fun i _ => hT3 i, sum_const, smul_eq_mul]
  rw [hd2] at hsplit
  rw [mul_assoc 3 (#E) p]
  omega

theorem hered {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (hk : 3 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (hb : ∀ A, #(L A) ≤ 2) (P : Finset U) (hP : k ≤ #P) :
    (#P - k) * 2 ^ k * (#P).choose (k - 1) ≤
      12 * (#P - k + 2) * ∑ W ∈ P.powersetCard (k - 1), (2 ^ k - #(W.powerset.biUnion L)) := by
  classical
  set D := fun W : Finset U => 2 ^ k - #(W.powerset.biUnion L) with hDdef
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, #P = m + 3 + t := ⟨#P - (m + 3), by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e3 : m + 3 - 3 = m := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  rw [e1]
  set p := 2 ^ (m + 1) with hp
  have hn : 2 ^ (m + 3) = 4 * p := by rw [hp, pow_add 2 m 3, pow_add 2 m 1]; ring
  -- double counting identity
  have hdc : ∑ W ∈ P.powersetCard (m + 2), ∑ _q ∈ W.offDiag, D W =
      ∑ B ∈ P.powersetCard m, ∑ q ∈ (P \ B).offDiag, D (insert q.1 (insert q.2 B)) := by
    rw [sum_comm' (t' := P.offDiag)
      (s' := fun q => (P.powersetCard (m + 2)).filter (fun W => q.1 ∈ W ∧ q.2 ∈ W))]
    · rw [sum_comm' (t' := P.offDiag)
        (s' := fun q => (P.powersetCard m).filter (fun B => q.1 ∉ B ∧ q.2 ∉ B))]
      · refine sum_congr rfl fun q hq => ?_
        rw [mem_offDiag] at hq
        obtain ⟨hi, hj, hij⟩ := hq
        refine sum_nbij' (fun W => (W.erase q.1).erase q.2) (fun B => insert q.1 (insert q.2 B))
          ?_ ?_ ?_ ?_ ?_
        · intro W hW
          simp only [mem_filter, mem_powersetCard] at hW ⊢
          refine ⟨⟨(erase_subset _ _).trans ((erase_subset _ _).trans hW.1.1), ?_⟩, ?_, ?_⟩
          · rw [card_erase_of_mem (mem_erase.2 ⟨Ne.symm hij, hW.2.2⟩), card_erase_of_mem hW.2.1,
              hW.1.2]; omega
          · simp [hij]
          · simp
        · intro B hB
          simp only [mem_filter, mem_powersetCard] at hB ⊢
          refine ⟨⟨insert_subset hi (insert_subset hj hB.1.1), ?_⟩, by simp, by simp⟩
          rw [card_insert_of_notMem (by simp [hij, hB.2.1]), card_insert_of_notMem hB.2.2, hB.1.2]
        · intro W hW
          simp only [mem_filter, mem_powersetCard] at hW
          rw [insert_erase (mem_erase.2 ⟨Ne.symm hij, hW.2.2⟩), insert_erase hW.2.1]
        · intro B hB
          simp only [mem_filter, mem_powersetCard] at hB
          rw [erase_insert (by simp [hij, hB.2.1]), erase_insert hB.2.2]
        · intro W hW
          simp only [mem_filter, mem_powersetCard] at hW
          rw [insert_erase (mem_erase.2 ⟨Ne.symm hij, hW.2.2⟩), insert_erase hW.2.1]
      · intro B q
        simp only [mem_powersetCard, mem_offDiag, mem_filter, mem_sdiff]
        constructor
        · rintro ⟨hB, ⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩; exact ⟨⟨hB, h2, h4⟩, h1, h3, h5⟩
        · rintro ⟨⟨hB, h2, h4⟩, h1, h3, h5⟩; exact ⟨hB, ⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
    · intro W q
      simp only [mem_powersetCard, mem_offDiag, mem_filter]
      constructor
      · rintro ⟨hW, h1, h2, h3⟩; exact ⟨⟨hW, h1, h2⟩, hW.1 h1, hW.1 h2, h3⟩
      · rintro ⟨⟨hW, h1, h2⟩, -, -, h3⟩; exact ⟨hW, h1, h2, h3⟩
  have hleft : ∑ W ∈ P.powersetCard (m + 2), ∑ _q ∈ W.offDiag, D W =
      (m + 2) * (m + 1) * ∑ W ∈ P.powersetCard (m + 2), D W := by
    rw [mul_sum]
    refine sum_congr rfl fun W hW => ?_
    rw [mem_powersetCard] at hW
    rw [sum_const, offDiag_card, hW.2, smul_eq_mul]
    congr 1
    rw [show (m + 2) * (m + 2) - (m + 2) = (m + 2) * (m + 1) by
      rw [show (m + 2) * (m + 2) = (m + 2) * (m + 1) + (m + 2) by ring]; omega]
  -- per-B bound summed
  have hper : ∀ B ∈ P.powersetCard m, (t + 3) ^ 2 * p ≤
      3 * ∑ q ∈ (P \ B).offDiag, D (insert q.1 (insert q.2 B)) + 3 * (t + 3) * p := by
    intro B hB
    rw [mem_powersetCard] at hB
    have hcard : #(P \ B) = t + 3 := by rw [card_sdiff_of_subset hB.1, ht, hB.2]; omega
    have := perB L (m + 3) hk hC hb B (P \ B) (by rw [hB.2]; omega) disjoint_sdiff
    rw [hcard, e2] at this
    exact this
  have hsum := sum_le_sum hper
  rw [sum_const, card_powersetCard, smul_eq_mul, sum_add_distrib, ← mul_sum, sum_const,
    card_powersetCard, smul_eq_mul, ← hdc, hleft, ht] at hsum
  -- binomial identity
  set M := (m + 3 + t).choose m with hM
  have hbin : (m + 3 + t).choose (m + 2) * ((m + 2) * (m + 1)) = M * ((t + 3) * (t + 2)) := by
    have a1 := Nat.choose_succ_right_eq (m + 3 + t) (m + 1)
    have a2 := Nat.choose_succ_right_eq (m + 3 + t) m
    rw [show m + 3 + t - (m + 1) = t + 2 by omega] at a1
    rw [show m + 3 + t - m = t + 3 by omega] at a2
    calc (m + 3 + t).choose (m + 2) * ((m + 2) * (m + 1))
        = ((m + 3 + t).choose (m + 1 + 1) * (m + 1 + 1)) * (m + 1) := by ring
      _ = (m + 3 + t).choose (m + 1) * (t + 2) * (m + 1) := by rw [a1]
      _ = ((m + 3 + t).choose (m + 1) * (m + 1)) * (t + 2) := by ring
      _ = M * (t + 3) * (t + 2) := by rw [a2]
      _ = M * ((t + 3) * (t + 2)) := by ring
  set S := ∑ W ∈ P.powersetCard (m + 2), D W with hS
  rw [ht, show m + 3 + t - (m + 3) = t by omega, hn]
  -- hsum : M * ((t+3)^2 * p) ≤ 3 * ((m+2)(m+1) S) + M * (3 (t+3) p)
  have key : M * ((t + 3) * p * t) ≤ 3 * ((m + 2) * (m + 1) * S) := by
    have : M * ((t + 3) ^ 2 * p) = M * ((t + 3) * p * t) + M * (3 * (t + 3) * p) := by ring
    omega
  have hc : 0 < (m + 2) * (m + 1) := by positivity
  apply Nat.le_of_mul_le_mul_right _ hc
  calc t * (4 * p) * (m + 3 + t).choose (m + 2) * ((m + 2) * (m + 1))
      = 4 * (t + 2) * (M * ((t + 3) * p * t)) := by
        rw [mul_assoc, hbin]; ring
    _ ≤ 4 * (t + 2) * (3 * ((m + 2) * (m + 1) * S)) := Nat.mul_le_mul_left _ key
    _ = 12 * (t + 2) * S * ((m + 2) * (m + 1)) := by ring
end E624R15H

namespace Erdos624

theorem hereditary_deficit_bound {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (hk : 3 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (hb : ∀ A, #(L A) ≤ 2) (P : Finset U) (hP : k ≤ #P) :
    (#P - k) * 2 ^ k * (#P).choose (k - 1) ≤
      12 * (#P - k + 2) * ∑ W ∈ P.powersetCard (k - 1), (2 ^ k - #(W.powerset.biUnion L)) := by
  exact E624R15H.hered L k hk hC hb P hP

end Erdos624

open Finset

theorem solution {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (hk : 3 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (hb : ∀ A, #(L A) ≤ 2) (P : Finset U) (hP : k ≤ #P) :
    (#P - k) * 2 ^ k * (#P).choose (k - 1) ≤
      12 * (#P - k + 2) * ∑ W ∈ P.powersetCard (k - 1), (2 ^ k - #(W.powerset.biUnion L)) :=
  Erdos624.hereditary_deficit_bound L k hk hC hb P hP
