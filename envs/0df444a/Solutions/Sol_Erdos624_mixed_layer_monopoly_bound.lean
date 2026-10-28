-- Prove2me | solution 1 for Erdos624.mixed_layer_monopoly_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T20:29:58.589533+00:00
-- url     : https://prove2.me/submissions/c7590bb4-05c6-4ebc-9d3d-3c0a02db5d02

import Mathlib
open Finset

namespace E624R15M
open Finset

lemma sum_ident (N m : ℕ) (hN : m + 1 ≤ N) :
    2 * ∑ b ∈ range (m + 1), (N - b) * m.choose b = (2 * N - m) * 2 ^ m := by
  have h1 : ∑ b ∈ range (m + 1), (N - b) * m.choose b =
      ∑ b ∈ range (m + 1), (N - m + b) * m.choose b := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun b hb => ?_
    rw [mem_range] at hb
    rw [show m + 1 - 1 - b = m - b by omega, Nat.choose_symm (by omega)]
    congr 1; omega
  rw [two_mul]
  nth_rewrite 2 [h1]
  rw [← sum_add_distrib, ← Nat.sum_range_choose, mul_sum]
  refine sum_congr rfl fun b hb => ?_
  rw [mem_range] at hb
  rw [← add_mul]; congr 1; omega

theorem mix {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (k j : ℕ) (hC : Fintype.card C = 2 ^ k)
    (hb : ∀ A, #(L A) ≤ 2) (Z : Finset U) (hZ : k ≤ #Z) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (v0 v1 : C) (hv : v0 ≠ v1) (hv0 : v0 ∉ L ∅) (hv1 : v1 ∉ L ∅)
    (hmon : ∀ A ⊆ Z, #A = j → L A = {v0, v1})
    (hDC : ∀ a, 1 ≤ a → a ≤ k → ∀ G : Finset (Finset U), (∀ A ∈ G, A ⊆ Z ∧ #A = a) →
      (∀ Y ⊆ Z, #Y = k → ∃ A ∈ G, A ⊆ Y) →
      (#Z - k + 1) * (#Z).choose a ≤ #G * ((#Z - a + 1) * (k - 1).choose (a - 1))) :
    2 * ((#Z - j + 1) * (k - 1).choose (j - 1)) ≤
      (#Z - k + 1) * (#((univ : Finset C).filter (fun u : C => u ∉ L ∅ ∧ u ≠ v0 ∧ u ≠ v1 ∧
        ∀ a ∈ Icc (1 : ℕ) k, ∃ Y ∈ Z.powersetCard k, ∀ A ∈ Y.powersetCard a, u ∉ L A)) + #(L ∅) + 2) +
      2 ^ (k - 1) * (k - 1) := by
  set N := #Z with hN
  set c : ℕ → ℕ := fun a => (N - a + 1) * (k - 1).choose (a - 1) with hc
  set rest := univ.filter (fun u => u ∉ L ∅ ∧ u ≠ v0 ∧ u ≠ v1) with hrest
  set Mz := univ.filter (fun u => u ∉ L ∅ ∧ u ≠ v0 ∧ u ≠ v1 ∧
        ∀ a ∈ Icc (1 : ℕ) k, ∃ Y ∈ Z.powersetCard k, ∀ A ∈ Y.powersetCard a, u ∉ L A) with hMz
  set Pr := rest.filter (fun u => ¬ ∀ a ∈ Icc (1 : ℕ) k, ∃ Y ∈ Z.powersetCard k, ∀ A ∈ Y.powersetCard a, u ∉ L A)
    with hPr
  have hrestc : #rest + (#(L ∅) + 2) = 2 ^ k := by
    have e : rest = univ \ (L ∅ ∪ {v0, v1}) := by
      ext u; simp [hrest, not_or]; tauto
    have hd : Disjoint (L ∅) {v0, v1} := by
      rw [disjoint_left]; intro u hu h
      simp only [mem_insert, mem_singleton] at h
      rcases h with rfl | rfl
      · exact hv0 hu
      · exact hv1 hu
    rw [e, card_sdiff_of_subset (subset_univ _), card_univ, hC, card_union_of_disjoint hd,
      card_pair hv]
    have hle : #(L ∅ ∪ {v0, v1}) ≤ 2 ^ k := by rw [← hC]; exact card_le_univ _
    rw [card_union_of_disjoint hd, card_pair hv] at hle
    omega
  have hsplit : #rest = #Mz + #Pr := by
    rw [← card_filter_add_card_filter_not (s := rest)
      (p := fun u => ∀ a ∈ Icc (1 : ℕ) k, ∃ Y ∈ Z.powersetCard k, ∀ A ∈ Y.powersetCard a, u ∉ L A)]
    congr 1
    rw [hrest, hMz, filter_filter]
    congr 1; ext u; simp [and_assoc]
  -- prunable colours choose a size
  have hpr : ∀ u ∈ Pr, ∃ a ∈ Icc 1 k, ∀ Y ⊆ Z, #Y = k → ∃ A ⊆ Y, #A = a ∧ u ∈ L A := by
    intro u hu
    rw [hPr, mem_filter] at hu
    push_neg at hu
    obtain ⟨a, ha, h⟩ := hu.2
    exact ⟨a, ha, fun Y hY hYk => by
      obtain ⟨A, hA, huA⟩ := h Y (mem_powersetCard.2 ⟨hY, hYk⟩)
      rw [mem_powersetCard] at hA
      exact ⟨A, hA.1, hA.2, huA⟩⟩
  choose! asz hasz1 hasz2 using hpr
  obtain ⟨Y0, hY0, hY0c⟩ := exists_subset_card_eq hZ
  have hne : ∀ u ∈ Pr, asz u ∈ (Icc 1 k).erase j := by
    intro u hu
    refine mem_erase.2 ⟨fun h => ?_, hasz1 u hu⟩
    obtain ⟨A, hA, hAa, huA⟩ := hasz2 u hu Y0 hY0 hY0c
    rw [h] at hAa
    rw [hmon A (hA.trans hY0) hAa] at huA
    have hu' := (mem_filter.1 (mem_filter.1 hu).1).2
    simp only [mem_insert, mem_singleton] at huA
    rcases huA with rfl | rfl
    · exact hu'.2.1 rfl
    · exact hu'.2.2 rfl
  have hfib := card_eq_sum_card_fiberwise hne
  -- per-size bound
  have hq : ∀ a ∈ (Icc 1 k).erase j, #(Pr.filter (fun u => asz u = a)) * (N - k + 1) ≤ 2 * c a := by
    intro a ha
    have ha' := mem_Icc.1 (mem_of_mem_erase ha)
    set Q := Pr.filter (fun u => asz u = a) with hQ
    set G := fun u => (Z.powersetCard a).filter (fun A => u ∈ L A) with hG
    have hdc : ∀ u ∈ Q, (N - k + 1) * N.choose a ≤ #(G u) * c a := by
      intro u hu
      rw [hQ, mem_filter] at hu
      refine hDC a ha'.1 ha'.2 (G u) (fun A hA => ?_) (fun Y hY hYk => ?_)
      · rw [hG, mem_filter, mem_powersetCard] at hA; exact hA.1
      · obtain ⟨A, hA, hAa, huA⟩ := hasz2 u hu.1 Y hY hYk
        rw [hu.2] at hAa
        exact ⟨A, by rw [hG, mem_filter, mem_powersetCard]; exact ⟨⟨hA.trans hY, hAa⟩, huA⟩, hA⟩
    have hs1 := sum_le_sum hdc
    rw [sum_const, smul_eq_mul, ← sum_mul] at hs1
    have hinc : ∑ u ∈ Q, #(G u) ≤ 2 * N.choose a := by
      have : ∑ u ∈ Q, #(G u) = ∑ A ∈ Z.powersetCard a, #(Q.filter (fun u => u ∈ L A)) := by
        simp only [hG, card_filter]
        rw [sum_comm]
      rw [this]
      calc ∑ A ∈ Z.powersetCard a, #(Q.filter (fun u => u ∈ L A))
          ≤ ∑ _A ∈ Z.powersetCard a, 2 := sum_le_sum fun A _ =>
            (card_le_card (fun u hu => (mem_filter.1 hu).2)).trans (hb A)
        _ = 2 * N.choose a := by rw [sum_const, card_powersetCard, smul_eq_mul, mul_comm]
    have hpos : 0 < N.choose a := Nat.choose_pos (by omega)
    have : #Q * (N - k + 1) * N.choose a ≤ 2 * c a * N.choose a := by
      calc #Q * (N - k + 1) * N.choose a = #Q * ((N - k + 1) * N.choose a) := by ring
        _ ≤ (∑ u ∈ Q, #(G u)) * c a := hs1
        _ ≤ (2 * N.choose a) * c a := Nat.mul_le_mul_right _ hinc
        _ = 2 * c a * N.choose a := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have hsum1 : #Pr * (N - k + 1) ≤ ∑ a ∈ (Icc 1 k).erase j, 2 * c a := by
    rw [hfib, sum_mul]; exact sum_le_sum hq
  have hjmem : j ∈ Icc 1 k := mem_Icc.2 ⟨hj1, hjk⟩
  have hsum2 := sum_erase_add (Icc 1 k) (fun a => 2 * c a) hjmem
  -- the exact binomial sum
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hId : ∑ a ∈ Icc 1 (m + 1), 2 * c a = (2 * N - m) * 2 ^ m := by
    rw [← mul_sum, ← sum_ident N m (by omega)]
    congr 1
    rw [show Icc 1 (m + 1) = Ico 1 (m + 2) by rfl, sum_Ico_eq_sum_range,
      show m + 2 - 1 = m + 1 by omega]
    refine sum_congr rfl fun b hb => ?_
    rw [hc]; simp only
    rw [show m + 1 - 1 = m by omega, show 1 + b - 1 = b by omega,
      show N - (1 + b) + 1 = N - b by rw [mem_range] at hb; omega]
  simp only [show m + 1 - 1 = m by omega] at hsum2 ⊢
  rw [hId] at hsum2
  have hX : N - (m + 1) + 1 = N - m := by omega
  rw [hX] at hsum1 ⊢
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  rw [hpow] at hrestc
  have e2 : (2 * N - m) * 2 ^ m = (N - m) * (2 * 2 ^ m) + 2 ^ m * m := by
    have : 2 * N - m = 2 * (N - m) + m := by omega
    rw [this]; ring
  have e1 : (N - m) * (2 * 2 ^ m) = (N - m) * #Pr + (N - m) * (#Mz + #(L ∅) + 2) := by
    rw [← hrestc, hsplit]; ring
  have hc' : 2 * ((N - j + 1) * m.choose (j - 1)) = 2 * c j := rfl
  rw [hc']
  linarith
end E624R15M

namespace Erdos624

theorem mixed_layer_monopoly_bound {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (k j : ℕ) (hC : Fintype.card C = 2 ^ k)
    (hb : ∀ A, #(L A) ≤ 2) (Z : Finset U) (hZ : k ≤ #Z) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (v0 v1 : C) (hv : v0 ≠ v1) (hv0 : v0 ∉ L ∅) (hv1 : v1 ∉ L ∅)
    (hmon : ∀ A ⊆ Z, #A = j → L A = {v0, v1})
    (hDC : ∀ a, 1 ≤ a → a ≤ k → ∀ G : Finset (Finset U), (∀ A ∈ G, A ⊆ Z ∧ #A = a) →
      (∀ Y ⊆ Z, #Y = k → ∃ A ∈ G, A ⊆ Y) →
      (#Z - k + 1) * (#Z).choose a ≤ #G * ((#Z - a + 1) * (k - 1).choose (a - 1))) :
    2 * ((#Z - j + 1) * (k - 1).choose (j - 1)) ≤
      (#Z - k + 1) * (#((univ : Finset C).filter (fun u : C => u ∉ L ∅ ∧ u ≠ v0 ∧ u ≠ v1 ∧
        ∀ a ∈ Icc (1 : ℕ) k, ∃ Y ∈ Z.powersetCard k, ∀ A ∈ Y.powersetCard a, u ∉ L A)) + #(L ∅) + 2) +
      2 ^ (k - 1) * (k - 1) := by
  exact E624R15M.mix L k j hC hb Z hZ hj1 hjk v0 v1 hv hv0 hv1 hmon hDC

end Erdos624

open Finset

theorem solution {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (k j : ℕ) (hC : Fintype.card C = 2 ^ k)
    (hb : ∀ A, #(L A) ≤ 2) (Z : Finset U) (hZ : k ≤ #Z) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (v0 v1 : C) (hv : v0 ≠ v1) (hv0 : v0 ∉ L ∅) (hv1 : v1 ∉ L ∅)
    (hmon : ∀ A ⊆ Z, #A = j → L A = {v0, v1})
    (hDC : ∀ a, 1 ≤ a → a ≤ k → ∀ G : Finset (Finset U), (∀ A ∈ G, A ⊆ Z ∧ #A = a) →
      (∀ Y ⊆ Z, #Y = k → ∃ A ∈ G, A ⊆ Y) →
      (#Z - k + 1) * (#Z).choose a ≤ #G * ((#Z - a + 1) * (k - 1).choose (a - 1))) :
    2 * ((#Z - j + 1) * (k - 1).choose (j - 1)) ≤
      (#Z - k + 1) * (#((univ : Finset C).filter (fun u : C => u ∉ L ∅ ∧ u ≠ v0 ∧ u ≠ v1 ∧
        ∀ a ∈ Icc (1 : ℕ) k, ∃ Y ∈ Z.powersetCard k, ∀ A ∈ Y.powersetCard a, u ∉ L A)) + #(L ∅) + 2) +
      2 ^ (k - 1) * (k - 1) :=
  Erdos624.mixed_layer_monopoly_bound L k j hC hb Z hZ hj1 hjk v0 v1 hv hv0 hv1 hmon hDC
