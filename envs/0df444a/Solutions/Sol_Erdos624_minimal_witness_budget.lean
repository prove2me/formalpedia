-- Prove2me | solution 1 for Erdos624.minimal_witness_budget
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T13:44:42.519372+00:00
-- url     : https://prove2.me/submissions/63fc096e-1c6e-4d73-b323-50f39855be85

import Mathlib

namespace Erdos624

open Finset

lemma choose_le_add_add (a b : ℕ) : ∀ t : ℕ, a.choose b ≤ (a + t).choose (b + t)
  | 0 => le_rfl
  | t + 1 => by
    have ih := choose_le_add_add a b t
    rw [show a + (t + 1) = (a + t) + 1 by omega, show b + (t + 1) = (b + t) + 1 by omega,
      Nat.choose_succ_succ]
    omega

lemma faces_containing_le {U : Type*} [Fintype U] [DecidableEq U] (M : Finset U) (k s : ℕ)
    (hs : s < k) (hM : s < M.card) :
    ((univ : Finset U).powersetCard k |>.filter (fun Y => M ⊆ Y)).card
      ≤ (Fintype.card U - s - 1).choose (k - s - 1) := by
  rcases Nat.lt_or_ge k M.card with hk | hk
  · have : ((univ : Finset U).powersetCard k |>.filter (fun Y => M ⊆ Y)) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro Y hY hMY
      have := Finset.card_le_card hMY
      rw [(Finset.mem_powersetCard.1 hY).2] at this
      omega
    rw [this]; simp
  · have hmn : M.card ≤ Fintype.card U := Finset.card_le_univ M
    have h1 : ((univ : Finset U).powersetCard k |>.filter (fun Y => M ⊆ Y)).card
        ≤ (Fintype.card U - M.card).choose (k - M.card) := by
      have := Finset.card_le_card_of_injOn (fun Y => Y \ M)
        (t := (univ \ M).powersetCard (k - M.card))
        (s := ((univ : Finset U).powersetCard k |>.filter (fun Y => M ⊆ Y))) ?_ ?_
      · rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ M),
          Finset.card_univ] at this
        exact this
      · intro Y hY
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hY
        rw [Finset.mem_coe, Finset.mem_powersetCard]
        refine ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl, ?_⟩
        rw [Finset.card_sdiff_of_subset hY.2, hY.1.2]
      · intro Y hY Y' hY' h
        rw [Finset.mem_coe, Finset.mem_filter] at hY hY'
        have e1 := Finset.sdiff_union_of_subset hY.2
        have e2 := Finset.sdiff_union_of_subset hY'.2
        simp only at h
        rw [← e1, ← e2, h]
    refine h1.trans ?_
    have := choose_le_add_add (Fintype.card U - M.card) (k - M.card) (M.card - (s + 1))
    rw [show Fintype.card U - M.card + (M.card - (s + 1)) = Fintype.card U - s - 1 by omega,
      show k - M.card + (M.card - (s + 1)) = k - s - 1 by omega] at this
    exact this

lemma small_subsets_card {U : Type*} [DecidableEq U] (Y : Finset U) (s : ℕ) :
    (Y.powerset.filter (fun A => A.card ≤ s)).card ≤ ∑ i ∈ range (s + 1), Y.card.choose i := by
  have : Y.powerset.filter (fun A => A.card ≤ s)
      = (range (s + 1)).biUnion (fun i => Y.powersetCard i) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨A.card, by omega, h1, rfl⟩
    · rintro ⟨i, hi, h1, rfl⟩; exact ⟨h1, by omega⟩
  rw [this]
  refine Finset.card_biUnion_le.trans (le_of_eq ?_)
  simp [Finset.card_powersetCard]

/-- Per-face bound. -/
lemma budget_face {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (L : Finset U → Finset C) (q k s : ℕ) (hq : ∀ A, (L A).card ≤ q) (S : Finset C)
    (Y : Finset U) (hYk : Y.card = k) (hcov : ∀ u ∈ S, ∃ A ⊆ Y, u ∈ L A) :
    S.card ≤ q * (∑ i ∈ range (s + 1), k.choose i)
      + ∑ u ∈ S, ((univ : Finset (Finset U)).filter
          (fun M => u ∈ L M ∧ (∀ A ⊂ M, u ∉ L A) ∧ s < M.card) |>.filter (fun M => M ⊆ Y)).card := by
  set small := (Y.powerset.filter (fun A => A.card ≤ s)).biUnion L
  set p : C → Prop := fun u => ∃ M, (u ∈ L M ∧ (∀ A ⊂ M, u ∉ L A) ∧ s < M.card) ∧ M ⊆ Y
  have hsub : S ⊆ small ∪ S.filter p := by
    intro u hu
    obtain ⟨A, hAY, huA⟩ := hcov u hu
    have hne : (Y.powerset.filter (fun B => u ∈ L B)).Nonempty :=
      ⟨A, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hAY, huA⟩⟩
    obtain ⟨M, hM, hmin⟩ := Finset.exists_min_image _ Finset.card hne
    rw [Finset.mem_filter, Finset.mem_powerset] at hM
    have hMmin : ∀ A ⊂ M, u ∉ L A := by
      intro A' hA' huA'
      have := hmin A' (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (hA'.1.trans hM.1), huA'⟩)
      have := Finset.card_lt_card hA'
      omega
    rcases Nat.lt_or_ge s M.card with h | h
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hu, M, ⟨hM.2, hMmin, h⟩, hM.1⟩)
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.2 ⟨M, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hM.1, h⟩, hM.2⟩
  have h1 : small.card ≤ q * (∑ i ∈ range (s + 1), k.choose i) := by
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_card_nsmul _ _ q (fun A _ => hq A)).trans ?_
    rw [smul_eq_mul, mul_comm]
    have := small_subsets_card Y s
    rw [hYk] at this
    exact Nat.mul_le_mul_left q this
  have h2 : (S.filter p).card ≤ ∑ u ∈ S, ((univ : Finset (Finset U)).filter
          (fun M => u ∈ L M ∧ (∀ A ⊂ M, u ∉ L A) ∧ s < M.card) |>.filter (fun M => M ⊆ Y)).card := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro u _
    split_ifs with hp
    · obtain ⟨M, hM1, hM2⟩ := hp
      exact Finset.card_pos.2 ⟨M, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hM1⟩, hM2⟩⟩
    · exact Nat.zero_le _
  calc S.card ≤ (small ∪ S.filter p).card := Finset.card_le_card hsub
    _ ≤ small.card + (S.filter p).card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add h1 h2

/-- **Minimal-witness counting budget.** Capacity-`q` list system on `U` (`|U| = n`),
`S` a set of colours covered on every `k`-face, `s < k`:
`|S| K ≤ q B_s(k) K + L_s Σ_{u∈S} m_u^{>s}` with `K = C(n,k)`, `B_s(k) = Σ_{i≤s} C(k,i)`,
`L_s = C(n-s-1, k-s-1)`, `m_u^{>s}` = number of inclusion-minimal witnesses of `u` of size `> s`. -/
theorem minimal_witness_budget {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (L : Finset U → Finset C) (q k s : ℕ) (hq : ∀ A, (L A).card ≤ q) (hs : s < k)
    (S : Finset C)
    (hcov : ∀ Y ∈ (univ : Finset U).powersetCard k, ∀ u ∈ S, ∃ A ⊆ Y, u ∈ L A) :
    S.card * (Fintype.card U).choose k
      ≤ q * (∑ i ∈ range (s + 1), k.choose i) * (Fintype.card U).choose k
        + (Fintype.card U - s - 1).choose (k - s - 1)
          * ∑ u ∈ S, ((univ : Finset (Finset U)).filter
              (fun M => u ∈ L M ∧ (∀ A ⊂ M, u ∉ L A) ∧ s < M.card)).card := by
  set F := (univ : Finset U).powersetCard k
  have hK : F.card = (Fintype.card U).choose k := by
    simp [F, Finset.card_powersetCard]
  set BM : C → Finset (Finset U) := fun u => (univ : Finset (Finset U)).filter
    (fun M => u ∈ L M ∧ (∀ A ⊂ M, u ∉ L A) ∧ s < M.card)
  have hface : ∀ Y ∈ F, S.card ≤ q * (∑ i ∈ range (s + 1), k.choose i)
      + ∑ u ∈ S, ((BM u).filter (fun M => M ⊆ Y)).card := fun Y hY =>
    budget_face L q k s hq S Y (Finset.mem_powersetCard.1 hY).2 (hcov Y hY)
  have hsum := Finset.sum_le_sum hface
  rw [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    hK] at hsum
  -- swap the double count
  have hswap : ∑ Y ∈ F, ∑ u ∈ S, ((BM u).filter (fun M => M ⊆ Y)).card
      = ∑ u ∈ S, ∑ M ∈ BM u, (F.filter (fun Y => M ⊆ Y)).card := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hbound : ∑ u ∈ S, ∑ M ∈ BM u, (F.filter (fun Y => M ⊆ Y)).card
      ≤ (Fintype.card U - s - 1).choose (k - s - 1) * ∑ u ∈ S, (BM u).card := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u _
    refine (Finset.sum_le_card_nsmul _ _ ((Fintype.card U - s - 1).choose (k - s - 1)) ?_).trans (le_of_eq ?_)
    · intro M hM
      exact faces_containing_le M k s hs (Finset.mem_filter.1 hM).2.2.2
    · rw [smul_eq_mul, mul_comm]
  rw [hswap] at hsum
  calc S.card * (Fintype.card U).choose k
      = (Fintype.card U).choose k * S.card := mul_comm _ _
    _ ≤ _ := hsum
    _ ≤ _ := by
      rw [mul_comm ((Fintype.card U).choose k) (q * _)]
      exact Nat.add_le_add_left hbound _

end Erdos624

open Finset

theorem solution {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (L : Finset U → Finset C) (q k s : ℕ) (hq : ∀ A, (L A).card ≤ q) (hs : s < k)
    (S : Finset C)
    (hcov : ∀ Y ∈ (univ : Finset U).powersetCard k, ∀ u ∈ S, ∃ A ⊆ Y, u ∈ L A) :
    S.card * (Fintype.card U).choose k
      ≤ q * (∑ i ∈ range (s + 1), k.choose i) * (Fintype.card U).choose k
        + (Fintype.card U - s - 1).choose (k - s - 1)
          * ∑ u ∈ S, ((univ : Finset (Finset U)).filter
              (fun M => u ∈ L M ∧ (∀ A ⊂ M, u ∉ L A) ∧ s < M.card)).card :=
  Erdos624.minimal_witness_budget L q k s hq hs S hcov
