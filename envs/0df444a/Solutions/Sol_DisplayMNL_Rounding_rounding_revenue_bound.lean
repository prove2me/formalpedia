-- Prove2me | solution 1 for DisplayMNL.Rounding.rounding_revenue_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:34:31.701321+00:00
-- url     : https://prove2.me/submissions/0a15d0ab-c8ea-4e97-960a-f1bfc65d3b3e

import Mathlib
import Definitions.Def_DisplayMNL_Rounding_Model
import Theorems.Thm_DisplayMNL_Rounding_ineq_16
import Theorems.Thm_DisplayMNL_Rounding_claim_5_5

open Finset

namespace RRBAux
open DisplayMNL.Rounding

theorem etil_mono {n : ℕ} (s : DPSeq n) (kmid : ℕ) : Monotone (etil s kmid) := by
  apply monotone_nat_of_le_succ
  intro j
  unfold etil
  apply Finset.card_le_card
  show U s kmid j ⊆ U s kmid j ∪ deltaStep s kmid (j + 1) (U s kmid j)
  exact Finset.subset_union_left

theorem rev_nonneg {n : ℕ} (I : Instance n) (hr : ∀ i, 0 < I.r i) (hw : ∀ i, 0 < I.w i)
    (S : Finset (Fin n)) : 0 ≤ rev I S := by
  unfold rev rhoSet wt rho
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ => (mul_pos (hr i) (hw i)).le)
  · have := Finset.sum_nonneg (fun i (_ : i ∈ S) => (hw i).le)
    linarith

theorem unimodal_min (f : ℕ → ℝ) (a b k : ℕ) (h : IsUnimodalOn f a b) (hak : a ≤ k)
    (hkb : k ≤ b) : min (f a) (f b) ≤ f k := by
  obtain ⟨m, ham, hmb, hinc, hdec⟩ := h
  rcases le_total k m with hkm | hkm
  · exact (min_le_left _ _).trans (hinc a k le_rfl hak hkm)
  · exact (min_le_right _ _).trans (hdec k b hkm hkb le_rfl)

end RRBAux

open DisplayMNL.Rounding in
theorem solution {n : ℕ} (I : Instance n) (ε : ℝ) (kmid : ℕ) (s : DPSeq n) (A : Fin n ≃ Fin n)
    (hst : Standing I ε) (hk1 : 1 ≤ kmid) (hk2 : kmid + 1 ≤ n)
    (hF : IsFeasible I ε kmid s) (hR : IsRounded I s kmid A) :
    (1 - 8 * ε) *
        ((∑ j ∈ Icc 1 (jmid s kmid),
            lamSum I (Itil s kmid j) * min (alpha I s j) (alpha I s (j + 1))) +
          ∑ j ∈ Icc (jmid s kmid + 1) s.T,
            lamSum I (Itil s kmid j) * min (alpha I s (j - 1)) (alpha I s j)) ≤
      totalRev I A := by
  obtain ⟨hn2, hr, hw, hlam, hε0, hε1⟩ := hst
  obtain ⟨hT1, _, ⟨he1, _⟩, ⟨heT, _⟩, _⟩ := hF
  set jm := jmid s kmid with hjm
  set T := s.T with hTdef
  -- bounds on j_mid
  have hP1 : (fun j => 1 ≤ j ∧ s.e j ≤ kmid) 1 := ⟨le_rfl, by rw [he1]; exact hk1⟩
  have hjm1 : 1 ≤ jm := Nat.le_findGreatest hT1 hP1
  have hjmT : jm + 1 ≤ T := by
    have hle : jm ≤ T := Nat.findGreatest_le _
    have hspec : 1 ≤ jm ∧ s.e jm ≤ kmid :=
      Nat.findGreatest_spec (P := fun j => 1 ≤ j ∧ s.e j ≤ kmid) hT1 hP1
    rcases Nat.lt_or_ge jm T with h | h
    · omega
    · have : jm = T := le_antisymm hle h
      rw [this] at hspec
      rw [hTdef, heT] at hspec
      omega
  have hmono := RRBAux.etil_mono s kmid
  -- unified minimum term
  let m : ℕ → ℝ := fun j =>
    if j ≤ jm then min (alpha I s j) (alpha I s (j + 1)) else min (alpha I s (j - 1)) (alpha I s j)
  have hsplit :
      (∑ j ∈ Icc 1 jm, lamSum I (Itil s kmid j) * min (alpha I s j) (alpha I s (j + 1))) +
        ∑ j ∈ Icc (jm + 1) T, lamSum I (Itil s kmid j) * min (alpha I s (j - 1)) (alpha I s j)
        = ∑ j ∈ Icc 1 T, lamSum I (Itil s kmid j) * m j := by
    have hU : Icc 1 T = Icc 1 jm ∪ Icc (jm + 1) T := by
      ext x; simp only [mem_Icc, mem_union]; omega
    have hD : Disjoint (Icc 1 jm) (Icc (jm + 1) T) := by
      rw [Finset.disjoint_left]; intro x hx hx'; simp only [mem_Icc] at hx hx'; omega
    rw [hU, Finset.sum_union hD]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj; simp only [mem_Icc] at hj
      simp only [m, if_pos hj.2]
    · apply Finset.sum_congr rfl
      intro j hj; simp only [mem_Icc] at hj
      have : ¬ j ≤ jm := by omega
      simp only [m, if_neg this]
  -- key pointwise bound
  have hkey : ∀ j ∈ Icc 1 T, ∀ k ∈ Itil s kmid j, (1 - 8 * ε) * m j ≤ revAt I A k := by
    intro j hj k hk
    simp only [mem_Icc] at hj
    by_cases hjj : j ≤ jm
    · have hjj' : j ≤ jmid s kmid := hjj
      rw [Itil, if_pos hjj', mem_filter, mem_Ico] at hk
      have h16 := ineq_16 I ε kmid s A ⟨hn2, hr, hw, hlam, hε0, hε1⟩ hk1 hk2
        ⟨hT1, ‹_›, ⟨he1, ‹_›⟩, ⟨heT, ‹_›⟩, ‹_›⟩ hR j hj.1 (by omega)
      have h55 := claim_5_5 I ε kmid s A ⟨hn2, hr, hw, hlam, hε0, hε1⟩ hk1 hk2
        ⟨hT1, ‹_›, ⟨he1, ‹_›⟩, ⟨heT, ‹_›⟩, ‹_›⟩ hR j hj.1 (by omega)
      have hu := RRBAux.unimodal_min _ _ _ k h55 hk.1.1 hk.1.2.le
      simp only [m, if_pos hjj]
      exact h16.trans hu
    · have hjj' : ¬ j ≤ jmid s kmid := hjj
      rw [Itil, if_neg hjj', mem_filter, mem_Ioc] at hk
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have h16 := ineq_16 I ε kmid s A ⟨hn2, hr, hw, hlam, hε0, hε1⟩ hk1 hk2
        ⟨hT1, ‹_›, ⟨he1, ‹_›⟩, ⟨heT, ‹_›⟩, ‹_›⟩ hR i (by omega) (by omega)
      have h55 := claim_5_5 I ε kmid s A ⟨hn2, hr, hw, hlam, hε0, hε1⟩ hk1 hk2
        ⟨hT1, ‹_›, ⟨he1, ‹_›⟩, ⟨heT, ‹_›⟩, ‹_›⟩ hR i (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hk
      have hu := RRBAux.unimodal_min _ _ _ k h55 hk.1.1.le hk.1.2
      simp only [m, if_neg hjj, Nat.add_sub_cancel]
      exact h16.trans hu
  -- positions lie in [1, n]
  have hsub : ∀ j ∈ Icc 1 T, Itil s kmid j ⊆ Icc 1 n := by
    intro j _ k hk
    simp only [mem_Icc]
    unfold Itil at hk
    split_ifs at hk
    · simp only [mem_filter] at hk; omega
    · simp only [mem_filter] at hk; omega
  -- pairwise disjoint
  have hdisj_lt : ∀ j j', j < j' → Disjoint (Itil s kmid j) (Itil s kmid j') := by
    intro j j' hjj'
    rw [Finset.disjoint_left]
    intro k hk hk'
    unfold Itil at hk hk'
    split_ifs at hk hk' with h1 h2 h2
    · simp only [mem_filter, mem_Ico] at hk hk'
      have := hmono (show j + 1 ≤ j' by omega)
      omega
    · simp only [mem_filter, mem_Ico, mem_Ioc] at hk hk'
      omega
    · omega
    · simp only [mem_filter, mem_Ioc] at hk hk'
      have := hmono (show j ≤ j' - 1 by omega)
      omega
  have hdisj : (↑(Icc 1 T) : Set ℕ).PairwiseDisjoint (Itil s kmid) := by
    intro j _ j' _ hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hdisj_lt j j' h
    · exact (hdisj_lt j' j h).symm
  have hnonneg : ∀ k ∈ Icc 1 n, 0 ≤ I.lam k * revAt I A k := by
    intro k hk
    simp only [mem_Icc] at hk
    exact mul_nonneg (hlam k hk.1 hk.2).le (RRBAux.rev_nonneg I hr hw _)
  rw [hsplit, Finset.mul_sum]
  calc ∑ j ∈ Icc 1 T, (1 - 8 * ε) * (lamSum I (Itil s kmid j) * m j)
      = ∑ j ∈ Icc 1 T, ∑ k ∈ Itil s kmid j, I.lam k * ((1 - 8 * ε) * m j) := by
        apply Finset.sum_congr rfl
        intro j _
        unfold lamSum
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _; ring
    _ ≤ ∑ j ∈ Icc 1 T, ∑ k ∈ Itil s kmid j, I.lam k * revAt I A k := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        have hkn := hsub j hj hk
        simp only [mem_Icc] at hkn
        exact mul_le_mul_of_nonneg_left (hkey j hj k hk) (hlam k hkn.1 hkn.2).le
    _ = ∑ k ∈ (Icc 1 T).biUnion (Itil s kmid), I.lam k * revAt I A k :=
        (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ k ∈ Icc 1 n, I.lam k * revAt I A k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_biUnion] at hk
          obtain ⟨j, hj, hk⟩ := hk
          exact hsub j hj hk
        · intro k hk _; exact hnonneg k hk
    _ = totalRev I A := rfl
