-- Prove2me | solution 1 for DetSupportRank.DeterminantSupport.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T04:05:00.326278+00:00
-- url     : https://prove2.me/submissions/845c7cb7-7760-4c84-8589-fc001535e2f1

import Definitions.Def_DetSupportRank_DeterminantSupport_DeterminantFamily

noncomputable section
open scoped BigOperators

namespace DetSupportRank_Proof

open Classical

/-! ### Section 1: Roots of Unity and Subset-Sum Hyperplane Avoidance -/

def zeta (n : ℕ) : ℂ :=
  Complex.exp (2 * ↑Real.pi * Complex.I / (n : ℂ))

lemma isPrimitiveRoot_zeta {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n (Nat.ne_of_gt hn)

def root (n : ℕ) (i : Fin n) : ℂ :=
  (zeta n) ^ (i : ℕ)

lemma zeta_mul_star (n : ℕ) : zeta n * star (zeta n) = 1 := by
  unfold zeta
  rw [show star (Complex.exp (2 * ↑Real.pi * Complex.I / (n : ℂ))) =
      Complex.exp (star (2 * ↑Real.pi * Complex.I / (n : ℂ))) from (Complex.exp_conj _).symm]
  rw [← Complex.exp_add]
  have h : 2 * (Real.pi : ℂ) * Complex.I / (n : ℂ) +
      star (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) = 0 := by
    simp [Complex.conj_ofReal]
    ring
  rw [h, Complex.exp_zero]

lemma root_mul_star {n : ℕ} (i : Fin n) : root n i * star (root n i) = 1 := by
  unfold root
  rw [star_pow, ← mul_pow, zeta_mul_star, one_pow]

lemma root_ne_zero {n : ℕ} (i : Fin n) : root n i ≠ 0 := by
  intro h
  have := root_mul_star i
  rw [h, zero_mul] at this
  exact zero_ne_one this

lemma root_pow_n {n : ℕ} (hn : 0 < n) (i : Fin n) : (root n i) ^ n = 1 := by
  unfold root
  rw [← pow_mul, mul_comm, pow_mul, (isPrimitiveRoot_zeta hn).pow_eq_one, one_pow]

lemma root_injective {n : ℕ} (hn : 0 < n) : Function.Injective (root n) := by
  intro i j hij
  ext
  exact (isPrimitiveRoot_zeta hn).pow_inj i.isLt j.isLt hij

lemma sum_univ_root {n : ℕ} (hn : 1 < n) : ∑ i : Fin n, root n i = 0 := by
  unfold root
  rw [Fin.sum_univ_eq_sum_range (fun k => (zeta n) ^ k)]
  exact (isPrimitiveRoot_zeta (by omega)).geom_sum_eq_zero hn

/-- Two pairs of unit-circle complex numbers with the same nonzero sum coincide. -/
lemma unit_circle_pair_unique {z₁ z₂ w₁ w₂ s : ℂ}
    (hz₁ : z₁ * star z₁ = 1) (hz₂ : z₂ * star z₂ = 1)
    (hw₁ : w₁ * star w₁ = 1) (hw₂ : w₂ * star w₂ = 1)
    (hs : s ≠ 0) (hzs : z₁ + z₂ = s) (hws : w₁ + w₂ = s) :
    (w₁ = z₁ ∧ w₂ = z₂) ∨ (w₁ = z₂ ∧ w₂ = z₁) := by
  have hstars : star s ≠ 0 := star_ne_zero.mpr hs
  have hprod_z : z₁ * z₂ * star s = s := by
    rw [← hzs, star_add]
    calc z₁ * z₂ * (star z₁ + star z₂)
        = (z₁ * star z₁) * z₂ + z₁ * (z₂ * star z₂) := by ring
      _ = 1 * z₂ + z₁ * 1 := by rw [hz₁, hz₂]
      _ = z₁ + z₂ := by ring
  have hprod_w : w₁ * w₂ * star s = s := by
    rw [← hws, star_add]
    calc w₁ * w₂ * (star w₁ + star w₂)
        = (w₁ * star w₁) * w₂ + w₁ * (w₂ * star w₂) := by ring
      _ = 1 * w₂ + w₁ * 1 := by rw [hw₁, hw₂]
      _ = w₁ + w₂ := by ring
  have hmul_eq : z₁ * z₂ = w₁ * w₂ :=
    mul_right_cancel₀ hstars (hprod_z.trans hprod_w.symm)
  have hadd_eq : z₁ + z₂ = w₁ + w₂ := hzs.trans hws.symm
  have hquad : (w₁ - z₁) * (w₁ - z₂) = 0 := by
    calc (w₁ - z₁) * (w₁ - z₂)
        = w₁ ^ 2 - (z₁ + z₂) * w₁ + z₁ * z₂ := by ring
      _ = w₁ ^ 2 - (w₁ + w₂) * w₁ + w₁ * w₂ := by rw [hadd_eq, hmul_eq]
      _ = 0 := by ring
  rcases mul_eq_zero.mp hquad with h1 | h2
  · left
    have hw1z1 : w₁ = z₁ := sub_eq_zero.mp h1
    exact ⟨hw1z1, by linear_combination -hadd_eq - hw1z1⟩
  · right
    have hw1z2 : w₁ = z₂ := sub_eq_zero.mp h2
    exact ⟨hw1z2, by linear_combination -hadd_eq - hw1z2⟩

def zeroSumSubsets (n k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.powersetCard k (Finset.univ : Finset (Fin n))).filter
    (fun B => ∑ i ∈ B, root n i = 0)

def N0 (n k : ℕ) : ℕ := (zeroSumSubsets n k).card

lemma N0_compl {n k : ℕ} (hn : 1 < n) (hk : k ≤ n) : N0 n k = N0 n (n - k) := by
  unfold N0 zeroSumSubsets
  refine Finset.card_bij (fun B _ => Finset.univ \ B) ?_ ?_ ?_
  · intro B hB
    simp only [Finset.mem_filter, Finset.mem_powersetCard_univ] at hB ⊢
    refine ⟨?_, ?_⟩
    · rw [Finset.card_sdiff_of_subset (Finset.subset_univ B), Finset.card_univ,
        Fintype.card_fin, hB.1]
    · have htot := Finset.sum_sdiff (Finset.subset_univ B) (f := root n)
      rw [sum_univ_root hn, hB.2, add_zero] at htot
      exact htot
  · intro B₁ _ B₂ _ h
    have h1 : Finset.univ \ (Finset.univ \ B₁) = Finset.univ \ (Finset.univ \ B₂) :=
      congrArg (Finset.univ \ ·) h
    simpa [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] using h1
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_powersetCard_univ] at hC
    refine ⟨Finset.univ \ C, ?_, Finset.sdiff_sdiff_eq_self (Finset.subset_univ C)⟩
    simp only [Finset.mem_filter, Finset.mem_powersetCard_univ]
    refine ⟨?_, ?_⟩
    · rw [Finset.card_sdiff_of_subset (Finset.subset_univ C), Finset.card_univ,
        Fintype.card_fin, hC.1]
      omega
    · have htot := Finset.sum_sdiff (Finset.subset_univ C) (f := root n)
      rw [sum_univ_root hn, hC.2, add_zero] at htot
      exact htot

lemma N0_one (n : ℕ) : N0 n 1 = 0 := by
  unfold N0 zeroSumSubsets
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro B hB
  rw [Finset.mem_powersetCard_univ, Finset.card_eq_one] at hB
  rcases hB with ⟨i, rfl⟩
  rw [Finset.sum_singleton]
  exact root_ne_zero i

lemma pair_sum_zero_eq_empty_of_odd {n : ℕ} (hn : Odd n) (S : Finset (Fin n)) :
    ((Finset.powersetCard 2 S).filter (fun P => ∑ i ∈ P, root n i = 0)) = ∅ := by
  have hn_pos : 0 < n := by rcases hn with ⟨k, rfl⟩; omega
  rw [Finset.filter_eq_empty_iff]
  intro P hP hsum
  rw [Finset.mem_powersetCard] at hP
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hP.2
  rw [Finset.sum_pair hij] at hsum
  have hneg : root n i = - root n j := eq_neg_of_add_eq_zero_left hsum
  have hp1 : (root n i) ^ n = 1 := root_pow_n hn_pos i
  rw [hneg, neg_pow, hn.neg_one_pow, root_pow_n hn_pos j, mul_one] at hp1
  norm_num at hp1

lemma N0_two_of_odd {n : ℕ} (hn : Odd n) : N0 n 2 = 0 := by
  unfold N0 zeroSumSubsets
  rw [pair_sum_zero_eq_empty_of_odd hn, Finset.card_empty]

lemma two_mul_pair_sum_zero_card_le {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) :
    2 * ((Finset.powersetCard 2 S).filter (fun P => ∑ i ∈ P, root n i = 0)).card ≤ S.card := by
  set Z := (Finset.powersetCard 2 S).filter (fun P => ∑ i ∈ P, root n i = 0)
  have hdisj : (Z : Set (Finset (Fin n))).PairwiseDisjoint id := by
    intro P₁ hP₁ P₂ hP₂ hne
    change Disjoint P₁ P₂
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    exfalso
    apply hne
    simp only [Z, Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hP₁ hP₂
    obtain ⟨a₁, b₁, hab₁, rfl⟩ := Finset.card_eq_two.mp hP₁.1.2
    obtain ⟨a₂, b₂, hab₂, rfl⟩ := Finset.card_eq_two.mp hP₂.1.2
    have hsum₁ : root n a₁ + root n b₁ = 0 := by simpa [Finset.sum_pair hab₁] using hP₁.2
    have hsum₂ : root n a₂ + root n b₂ = 0 := by simpa [Finset.sum_pair hab₂] using hP₂.2
    have hother₁ : ∃ y₁, ({a₁, b₁} : Finset (Fin n)) = {x, y₁} ∧ root n x + root n y₁ = 0 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx₁
      rcases hx₁ with rfl | rfl
      · exact ⟨b₁, rfl, hsum₁⟩
      · exact ⟨a₁, by rw [Finset.pair_comm], by rwa [add_comm] at hsum₁⟩
    have hother₂ : ∃ y₂, ({a₂, b₂} : Finset (Fin n)) = {x, y₂} ∧ root n x + root n y₂ = 0 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx₂
      rcases hx₂ with rfl | rfl
      · exact ⟨b₂, rfl, hsum₂⟩
      · exact ⟨a₂, by rw [Finset.pair_comm], by rwa [add_comm] at hsum₂⟩
    rcases hother₁ with ⟨y₁, hset₁, hy₁⟩
    rcases hother₂ with ⟨y₂, hset₂, hy₂⟩
    have hy_eq : root n y₁ = root n y₂ := add_left_cancel (hy₁.trans hy₂.symm)
    rw [hset₁, hset₂, root_injective hn hy_eq]
  have hcard : (Z.biUnion id).card = ∑ P ∈ Z, P.card := Finset.card_biUnion hdisj
  have htwo : ∑ P ∈ Z, P.card = 2 * Z.card := by
    have : ∀ P ∈ Z, P.card = 2 :=
      fun P hP => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).2
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]
  have hsub : Z.biUnion id ⊆ S := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    rcases hx with ⟨P, hP, hxP⟩
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).1 hxP
  linarith [Finset.card_le_card hsub]

lemma pair_sum_nonzero_card_le_one {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) {s : ℂ} (hs : s ≠ 0) :
    ((Finset.powersetCard 2 S).filter (fun P => ∑ i ∈ P, root n i = s)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro P₁ hP₁ P₂ hP₂
  simp only [Finset.mem_filter, Finset.mem_powersetCard] at hP₁ hP₂
  obtain ⟨i₁, i₂, hi, rfl⟩ := Finset.card_eq_two.mp hP₁.1.2
  obtain ⟨j₁, j₂, hj, rfl⟩ := Finset.card_eq_two.mp hP₂.1.2
  have hs₁ : root n i₁ + root n i₂ = s := by simpa [Finset.sum_pair hi] using hP₁.2
  have hs₂ : root n j₁ + root n j₂ = s := by simpa [Finset.sum_pair hj] using hP₂.2
  rcases unit_circle_pair_unique (root_mul_star i₁) (root_mul_star i₂)
      (root_mul_star j₁) (root_mul_star j₂) hs hs₁ hs₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [root_injective hn h1, root_injective hn h2]
  · rw [root_injective hn h1, root_injective hn h2, Finset.pair_comm]

lemma double_count_N0 {n k : ℕ} (hk2 : 2 ≤ k) :
    k.choose 2 * N0 n k =
      ∑ C ∈ Finset.powersetCard (k - 2) (Finset.univ : Finset (Fin n)),
        ((Finset.powersetCard 2 (Finset.univ \ C)).filter
          (fun P => ∑ i ∈ P, root n i = - ∑ i ∈ C, root n i)).card := by
  set U : Finset (Fin n) := Finset.univ
  set A := Finset.powersetCard (k - 2) U
  set Z := zeroSumSubsets n k
  have h1 : ∑ B ∈ Z, (A.filter (fun C => C ⊆ B)).card = k.choose 2 * N0 n k := by
    have hB : ∀ B ∈ Z, (A.filter (fun C => C ⊆ B)).card = k.choose 2 := by
      intro B hB
      have hcardB : B.card = k := Finset.mem_powersetCard_univ.mp (Finset.mem_filter.mp hB).1
      have hfilt : A.filter (fun C => C ⊆ B) = Finset.powersetCard (k - 2) B := by
        ext C
        simp only [A, U, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
        exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
      rw [hfilt, Finset.card_powersetCard, hcardB, Nat.choose_symm (by omega : 2 ≤ k)]
    rw [Finset.sum_congr rfl hB, Finset.sum_const, smul_eq_mul, mul_comm]
    rfl
  have hswap : ∑ B ∈ Z, (A.filter (fun C => C ⊆ B)).card =
      ∑ C ∈ A, (Z.filter (fun B => C ⊆ B)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [← h1, hswap]
  refine Finset.sum_congr rfl (fun C hC => ?_)
  have hcardC : C.card = k - 2 := Finset.mem_powersetCard_univ.mp hC
  refine Finset.card_bij (fun B _ => B \ C) ?_ ?_ ?_
  · intro B hB
    simp only [Z, zeroSumSubsets, Finset.mem_filter, Finset.mem_powersetCard_univ] at hB
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Finset.sdiff_subset_sdiff (Finset.subset_univ B) Finset.Subset.rfl
    · rw [Finset.card_sdiff_of_subset hB.2, hB.1.1, hcardC]
      omega
    · have hsum := Finset.sum_sdiff hB.2 (f := root n)
      rw [hB.1.2] at hsum
      exact eq_neg_of_add_eq_zero_left hsum
  · intro B₁ hB₁ B₂ hB₂ heq
    have hsub₁ : C ⊆ B₁ := (Finset.mem_filter.mp hB₁).2
    have hsub₂ : C ⊆ B₂ := (Finset.mem_filter.mp hB₂).2
    rw [← Finset.sdiff_union_of_subset hsub₁, ← Finset.sdiff_union_of_subset hsub₂, heq]
  · intro P hP
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hP
    have hdisj : Disjoint P C :=
      Finset.disjoint_left.mpr (fun x hxP hxC => (Finset.mem_sdiff.mp (hP.1.1 hxP)).2 hxC)
    refine ⟨P ∪ C, ?_, Finset.union_sdiff_cancel_right hdisj⟩
    simp only [Z, zeroSumSubsets, Finset.mem_filter, Finset.mem_powersetCard_univ]
    refine ⟨⟨?_, ?_⟩, Finset.subset_union_right⟩
    · rw [Finset.card_union_of_disjoint hdisj, hP.1.2, hcardC]
      omega
    · rw [Finset.sum_union hdisj, hP.2, neg_add_cancel]

lemma choose_two_mul_choose {n k : ℕ} (hk2 : 2 ≤ k) (hkn : k ≤ n) :
    (n - k + 2) * (n - k + 1) * n.choose (k - 2) = 2 * k.choose 2 * n.choose k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk2
  have hchoose2 : 2 * (2 + j).choose 2 = (j + 2) * (j + 1) := by
    rw [Nat.choose_two_right, show 2 + j - 1 = j + 1 by omega]
    have hdiv : 2 ∣ (2 + j) * (j + 1) := by
      rcases Nat.even_or_odd j with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact ⟨(m + 1) * (2 * m + 1), by ring⟩
      · exact ⟨(2 * m + 3) * (m + 1), by ring⟩
    rw [Nat.mul_div_cancel' hdiv]
    ring
  have hr1 : 2 + j - 2 = j := by omega
  have hr2 : n - (2 + j) + 2 = n - j := by omega
  have hr3 : n - (2 + j) + 1 = n - (j + 1) := by omega
  have hr4 : 2 + j = j + 2 := by omega
  rw [hr1, hr2, hr3, hchoose2, hr4]
  calc (n - j) * (n - (j + 1)) * n.choose j
      = (n - (j + 1)) * (n.choose j * (n - j)) := by ring
    _ = (n - (j + 1)) * (n.choose (j + 1) * (j + 1)) := by
        rw [← Nat.choose_succ_right_eq n j]
    _ = (j + 1) * (n.choose (j + 1) * (n - (j + 1))) := by ring
    _ = (j + 1) * (n.choose (j + 2) * (j + 2)) := by
        rw [← Nat.choose_succ_right_eq n (j + 1)]
    _ = (j + 2) * (j + 1) * n.choose (j + 2) := by ring

lemma N0_bound_half {n : ℕ} (hn : 2 < n) :
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ n →
      (if Odd n then n else n - 1) * N0 n k ≤ n.choose k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk1 hk2n
    by_cases hk_eq1 : k = 1
    · subst hk_eq1
      rw [N0_one, mul_zero]
      exact Nat.zero_le _
    by_cases hk_eq2 : k = 2
    · subst hk_eq2
      by_cases hodd : Odd n
      · rw [if_pos hodd, N0_two_of_odd hodd, mul_zero]
        exact Nat.zero_le _
      · rw [if_neg hodd]
        have h2 : 2 * N0 n 2 ≤ n := by
          simpa [N0, zeroSumSubsets] using
            two_mul_pair_sum_zero_card_le (by omega) (Finset.univ : Finset (Fin n))
        have hch2 : 2 * n.choose 2 = n * (n - 1) := by
          rw [Nat.choose_two_right]
          have hdiv : 2 ∣ n * (n - 1) := by
            have heven : Even n := Nat.not_odd_iff_even.mp hodd
            rcases heven with ⟨m, rfl⟩
            exact ⟨m * (m + m - 1), by ring⟩
          exact Nat.mul_div_cancel' hdiv
        have hmul : 2 * ((n - 1) * N0 n 2) ≤ 2 * n.choose 2 := by
          calc 2 * ((n - 1) * N0 n 2) = (n - 1) * (2 * N0 n 2) := by ring
            _ ≤ (n - 1) * n := Nat.mul_le_mul_left (n - 1) h2
            _ = 2 * n.choose 2 := by rw [hch2]; ring
        omega
    have hk3 : 3 ≤ k := by omega
    have hkn : k ≤ n := by omega
    have hk2_pos : 0 < 2 * k.choose 2 := by
      have : 0 < k.choose 2 := Nat.choose_pos (by omega)
      omega
    by_cases hodd : Odd n
    · rw [if_pos hodd]
      have hdc : k.choose 2 * N0 n k ≤ n.choose (k - 2) := by
        rw [double_count_N0 (by omega)]
        have hterm : ∀ C ∈ Finset.powersetCard (k - 2) (Finset.univ : Finset (Fin n)),
            ((Finset.powersetCard 2 (Finset.univ \ C)).filter
              (fun P => ∑ i ∈ P, root n i = - ∑ i ∈ C, root n i)).card ≤ 1 := by
          intro C _
          by_cases hs : - ∑ i ∈ C, root n i = 0
          · rw [hs, pair_sum_zero_eq_empty_of_odd hodd, Finset.card_empty]
            omega
          · exact pair_sum_nonzero_card_le_one (by omega) _ hs
        calc ∑ C ∈ Finset.powersetCard (k - 2) (Finset.univ : Finset (Fin n)),
              ((Finset.powersetCard 2 (Finset.univ \ C)).filter
                (fun P => ∑ i ∈ P, root n i = - ∑ i ∈ C, root n i)).card
            ≤ ∑ _C ∈ Finset.powersetCard (k - 2) (Finset.univ : Finset (Fin n)), 1 :=
              Finset.sum_le_sum hterm
          _ = n.choose (k - 2) := by
              simp [Finset.card_powersetCard]
      have hineq : 2 * n ≤ (n - k + 2) * (n - k + 1) := by
        set m := n - k
        have hm : n ≤ 2 * m := by omega
        nlinarith
      apply Nat.le_of_mul_le_mul_left _ hk2_pos
      calc 2 * k.choose 2 * (n * N0 n k)
          = 2 * n * (k.choose 2 * N0 n k) := by ring
        _ ≤ 2 * n * n.choose (k - 2) := Nat.mul_le_mul_left _ hdc
        _ ≤ (n - k + 2) * (n - k + 1) * n.choose (k - 2) := Nat.mul_le_mul_right _ hineq
        _ = 2 * k.choose 2 * n.choose k := choose_two_mul_choose (by omega) hkn
    · rw [if_neg hodd]
      set A := Finset.powersetCard (k - 2) (Finset.univ : Finset (Fin n))
      have hdc2 : 2 * (k.choose 2 * N0 n k) ≤
          2 * n.choose (k - 2) + (n - k) * N0 n (k - 2) := by
        rw [double_count_N0 (by omega), Finset.mul_sum]
        have hterm : ∀ C ∈ A,
            2 * ((Finset.powersetCard 2 (Finset.univ \ C)).filter
              (fun P => ∑ i ∈ P, root n i = - ∑ i ∈ C, root n i)).card ≤
              2 + (if ∑ i ∈ C, root n i = 0 then n - k else 0) := by
          intro C hC
          have hcardC : C.card = k - 2 := Finset.mem_powersetCard_univ.mp hC
          by_cases hs : ∑ i ∈ C, root n i = 0
          · rw [if_pos hs, show (- ∑ i ∈ C, root n i) = 0 by rw [hs, neg_zero]]
            have hle := two_mul_pair_sum_zero_card_le (by omega) (Finset.univ \ C)
            rw [Finset.card_sdiff_of_subset (Finset.subset_univ C), Finset.card_univ,
              Fintype.card_fin, hcardC] at hle
            omega
          · rw [if_neg hs]
            have hle := pair_sum_nonzero_card_le_one (by omega) (Finset.univ \ C)
              (neg_ne_zero.mpr hs)
            omega
        calc ∑ C ∈ A, 2 * ((Finset.powersetCard 2 (Finset.univ \ C)).filter
                (fun P => ∑ i ∈ P, root n i = - ∑ i ∈ C, root n i)).card
            ≤ ∑ C ∈ A, (2 + (if ∑ i ∈ C, root n i = 0 then n - k else 0)) :=
              Finset.sum_le_sum hterm
          _ = (∑ _C ∈ A, 2) + ∑ C ∈ A, (if ∑ i ∈ C, root n i = 0 then n - k else 0) :=
              Finset.sum_add_distrib
          _ = 2 * n.choose (k - 2) + (n - k) * N0 n (k - 2) := by
              have hA : ∑ _C ∈ A, 2 = 2 * n.choose (k - 2) := by
                simp [A, Finset.card_powersetCard, mul_comm]
              have hZ : ∑ C ∈ A, (if ∑ i ∈ C, root n i = 0 then n - k else 0) =
                  (n - k) * N0 n (k - 2) := by
                rw [← Finset.sum_filter]
                simp [N0, zeroSumSubsets, A, mul_comm]
              rw [hA, hZ]
      have hih : (n - 1) * N0 n (k - 2) ≤ n.choose (k - 2) := by
        simpa [if_neg hodd] using ih (k - 2) (by omega) (by omega) (by omega)
      have hineq : 2 * (n - 1) + (n - k) ≤ (n - k + 2) * (n - k + 1) := by
        set m := n - k
        have hm : n ≤ 2 * m := by omega
        have hn1 : n - 1 + 1 = n := by omega
        nlinarith
      apply Nat.le_of_mul_le_mul_left _ hk2_pos
      calc 2 * k.choose 2 * ((n - 1) * N0 n k)
          = (n - 1) * (2 * (k.choose 2 * N0 n k)) := by ring
        _ ≤ (n - 1) * (2 * n.choose (k - 2) + (n - k) * N0 n (k - 2)) :=
            Nat.mul_le_mul_left _ hdc2
        _ = 2 * (n - 1) * n.choose (k - 2) + (n - k) * ((n - 1) * N0 n (k - 2)) := by ring
        _ ≤ 2 * (n - 1) * n.choose (k - 2) + (n - k) * n.choose (k - 2) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ hih) _
        _ = (2 * (n - 1) + (n - k)) * n.choose (k - 2) := by ring
        _ ≤ (n - k + 2) * (n - k + 1) * n.choose (k - 2) := Nat.mul_le_mul_right _ hineq
        _ = 2 * k.choose 2 * n.choose k := choose_two_mul_choose (by omega) hkn

lemma N0_bound {n k : ℕ} (hn : 2 < n) (hk1 : 1 ≤ k) (hkn : k < n) :
    (if Odd n then n else n - 1) * N0 n k ≤ n.choose k := by
  by_cases h2k : 2 * k ≤ n
  · exact N0_bound_half hn k hk1 h2k
  · rw [N0_compl (by omega) (by omega), ← Nat.choose_symm (by omega : k ≤ n)]
    exact N0_bound_half hn (n - k) (by omega) (by omega)

lemma bad_perm_card_bound {n : ℕ} (hn : 2 < n) (A : Finset (Fin n))
    (hA_ne : A.Nonempty) (hA_univ : A ≠ Finset.univ) :
    (if Odd n then n else n - 1) *
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∑ i ∈ A, root n (σ i) = 0)).card ≤
        n.factorial := by
  set k := A.card
  have hk1 : 1 ≤ k := Finset.card_pos.mpr hA_ne
  have hkn : k < n := by
    have hle : A.card ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.subset_univ A)
    rw [Finset.card_univ, Fintype.card_fin] at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      apply hA_univ
      exact Finset.eq_of_subset_of_card_le (Finset.subset_univ A)
        (by rw [Finset.card_univ, Fintype.card_fin, heq])
  set Bad := Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∑ i ∈ A, root n (σ i) = 0)
  set Ac : Finset (Fin n) := Finset.univ \ A
  have hcardAc : Ac.card = n - k := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, Fintype.card_fin]
  have hB_mem : ∀ σ ∈ Bad, A.map σ.toEmbedding ∈ zeroSumSubsets n k := by
    intro σ hσ
    have hsum : ∑ i ∈ A, root n (σ i) = 0 := (Finset.mem_filter.mp hσ).2
    simp only [zeroSumSubsets, Finset.mem_filter, Finset.mem_powersetCard_univ]
    refine ⟨by rw [Finset.card_map], ?_⟩
    rwa [Finset.sum_map]
  -- Group `Bad` by `B = A.map σ.toEmbedding`
  have hBad_le : Bad.card ≤ N0 n k * (k.factorial * (n - k).factorial) := by
    have hpart : Bad.card = ∑ B ∈ zeroSumSubsets n k,
        (Bad.filter (fun σ => A.map σ.toEmbedding = B)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext σ
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        exact ⟨fun hσ => ⟨A.map σ.toEmbedding, hB_mem σ hσ, hσ, rfl⟩,
          fun ⟨_, _, hσ, _⟩ => hσ⟩
      · intro B₁ _ B₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro σ h₁ h₂
        exact hne ((Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2)
    rw [hpart]
    have hfiber : ∀ B ∈ zeroSumSubsets n k,
        (Bad.filter (fun σ => A.map σ.toEmbedding = B)).card ≤
          k.factorial * (n - k).factorial := by
      intro B hB
      have hcardB : B.card = k := Finset.mem_powersetCard_univ.mp (Finset.mem_filter.mp hB).1
      set Bc : Finset (Fin n) := Finset.univ \ B
      have hcardBc : Bc.card = n - k := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ B), Finset.card_univ,
          Fintype.card_fin, hcardB]
      let eB : ↥B ≃ Fin k := Fintype.equivFinOfCardEq (by simp [hcardB])
      let eBc : ↥Bc ≃ Fin (n - k) := Fintype.equivFinOfCardEq (by simp [hcardBc])
      let eA : Fin k ≃ ↥A := (Fintype.equivFinOfCardEq (by simp [k])).symm
      let eAc : Fin (n - k) ≃ ↥Ac := (Fintype.equivFinOfCardEq (by simp [hcardAc])).symm
      set Fib := Bad.filter (fun σ => A.map σ.toEmbedding = B)
      let φ : (σ : Equiv.Perm (Fin n)) → σ ∈ Fib →
          Equiv.Perm (Fin k) × Equiv.Perm (Fin (n - k)) := fun σ hσ =>
        have hmap : A.map σ.toEmbedding = B := (Finset.mem_filter.mp hσ).2
        have hfwdA : ∀ x : ↥A, σ x.1 ∈ B := fun x => by
          rw [← hmap]; exact Finset.mem_map_of_mem σ.toEmbedding x.2
        have hinvA : ∀ y : ↥B, σ.symm y.1 ∈ A := fun y => by
          have hy : y.1 ∈ A.map σ.toEmbedding := hmap ▸ y.2
          rcases Finset.mem_map.mp hy with ⟨x, hx, hxy⟩
          have : σ.symm y.1 = x := by rw [← hxy]; exact σ.symm_apply_apply x
          rwa [this]
        have hfwdAc : ∀ x : ↥Ac, σ x.1 ∈ Bc := fun x => by
          have hx : x.1 ∉ A := (Finset.mem_sdiff.mp x.2).2
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hmemB => hx ?_⟩
          simpa using hinvA ⟨σ x.1, hmemB⟩
        have hinvAc : ∀ y : ↥Bc, σ.symm y.1 ∈ Ac := fun y => by
          have hy : y.1 ∉ B := (Finset.mem_sdiff.mp y.2).2
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hmemA => hy ?_⟩
          simpa using hfwdA ⟨σ.symm y.1, hmemA⟩
        let isoA : ↥A ≃ ↥B :=
          { toFun := fun x => ⟨σ x.1, hfwdA x⟩
            invFun := fun y => ⟨σ.symm y.1, hinvA y⟩
            left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.1)
            right_inv := fun y => Subtype.ext (σ.apply_symm_apply y.1) }
        let isoAc : ↥Ac ≃ ↥Bc :=
          { toFun := fun x => ⟨σ x.1, hfwdAc x⟩
            invFun := fun y => ⟨σ.symm y.1, hinvAc y⟩
            left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.1)
            right_inv := fun y => Subtype.ext (σ.apply_symm_apply y.1) }
        (eA.trans (isoA.trans eB), eAc.trans (isoAc.trans eBc))
      have hinj : ∀ σ₁ (h₁ : σ₁ ∈ Fib) σ₂ (h₂ : σ₂ ∈ Fib),
          φ σ₁ h₁ = φ σ₂ h₂ → σ₁ = σ₂ := by
        intro σ₁ h₁ σ₂ h₂ heq
        have heq1 := (Prod.mk.inj heq).1
        have heq2 := (Prod.mk.inj heq).2
        apply Equiv.ext
        intro x
        by_cases hx : x ∈ A
        · have hk_eq := Equiv.congr_fun heq1 (eA.symm ⟨x, hx⟩)
          dsimp [φ] at hk_eq
          simp only [Equiv.trans_apply, Equiv.apply_symm_apply] at hk_eq
          exact congrArg Subtype.val (eB.injective hk_eq)
        · have hxAc : x ∈ Ac := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
          have hk_eq := Equiv.congr_fun heq2 (eAc.symm ⟨x, hxAc⟩)
          dsimp [φ] at hk_eq
          simp only [Equiv.trans_apply, Equiv.apply_symm_apply] at hk_eq
          exact congrArg Subtype.val (eBc.injective hk_eq)
      have hcard_prod : Fintype.card (Equiv.Perm (Fin k) × Equiv.Perm (Fin (n - k))) =
          k.factorial * (n - k).factorial := by
        rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm,
          Fintype.card_fin, Fintype.card_fin]
      rw [← hcard_prod, ← Finset.card_univ]
      exact Finset.card_le_card_of_injOn (fun σ => if h : σ ∈ Fib then φ σ h else (1, 1))
        (fun _ _ => Finset.mem_univ _)
        (fun σ₁ h₁ σ₂ h₂ h => by
          have h₁' : σ₁ ∈ Fib := h₁
          have h₂' : σ₂ ∈ Fib := h₂
          dsimp only at h
          rw [dif_pos h₁', dif_pos h₂'] at h
          exact hinj σ₁ h₁' σ₂ h₂' h)
    calc ∑ B ∈ zeroSumSubsets n k, (Bad.filter (fun σ => A.map σ.toEmbedding = B)).card
        ≤ ∑ _B ∈ zeroSumSubsets n k, (k.factorial * (n - k).factorial) :=
          Finset.sum_le_sum hfiber
      _ = N0 n k * (k.factorial * (n - k).factorial) := by
          simp [N0]
  calc (if Odd n then n else n - 1) * Bad.card
      ≤ (if Odd n then n else n - 1) * (N0 n k * (k.factorial * (n - k).factorial)) :=
        Nat.mul_le_mul_left _ hBad_le
    _ = ((if Odd n then n else n - 1) * N0 n k) * k.factorial * (n - k).factorial := by ring
    _ ≤ n.choose k * k.factorial * (n - k).factorial :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (N0_bound hn hk1 hkn))
    _ = n.factorial := Nat.choose_mul_factorial_mul_factorial (by omega)

lemma exists_perm_avoiding_hyperplanes {n r : ℕ} (hn : 2 < n)
    (hr : r < if Odd n then n else n - 1)
    (S : Fin r → Finset (Fin n))
    (hS : ∀ k, (S k).Nonempty ∧ S k ≠ Finset.univ) :
    ∃ π : Equiv.Perm (Fin n), ∀ k : Fin r, ∑ i ∈ S k, root n (π i) ≠ 0 := by
  set p := if Odd n then n else n - 1
  have hp_pos : 0 < p := by
    dsimp [p]; split_ifs <;> omega
  set BadUnion := Finset.univ.biUnion (fun k : Fin r =>
    Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∑ i ∈ S k, root n (σ i) = 0))
  have hlt : BadUnion.card < (Finset.univ : Finset (Equiv.Perm (Fin n))).card := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    have h1 : p * BadUnion.card ≤ p * n.factorial - 1 := by
      have hbu : BadUnion.card ≤ ∑ k : Fin r,
          (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
            ∑ i ∈ S k, root n (σ i) = 0)).card := Finset.card_biUnion_le
      have hmul : p * BadUnion.card ≤ r * n.factorial := by
        calc p * BadUnion.card
            ≤ p * ∑ k : Fin r,
                (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
                  ∑ i ∈ S k, root n (σ i) = 0)).card := Nat.mul_le_mul_left p hbu
          _ = ∑ k : Fin r, p * (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
                ∑ i ∈ S k, root n (σ i) = 0)).card := Finset.mul_sum _ _ _
          _ ≤ ∑ _k : Fin r, n.factorial :=
              Finset.sum_le_sum (fun k _ => bad_perm_card_bound hn (S k) (hS k).1 (hS k).2)
          _ = r * n.factorial := by simp
      have hnfac : 0 < n.factorial := Nat.factorial_pos n
      have hrp : r * n.factorial < p * n.factorial := Nat.mul_lt_mul_of_pos_right hr hnfac
      omega
    have hnfac : 0 < n.factorial := Nat.factorial_pos n
    have hlt_mul : p * BadUnion.card < p * n.factorial := by
      have : 0 < p * n.factorial := Nat.mul_pos hp_pos hnfac
      omega
    exact lt_of_mul_lt_mul_left hlt_mul (Nat.zero_le p)
  obtain ⟨π, _, hπ⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨π, fun k hk0 => hπ ?_⟩
  rw [Finset.mem_biUnion]
  exact ⟨k, Finset.mem_univ k, Finset.mem_filter.mpr ⟨Finset.mem_univ π, hk0⟩⟩

/-! ### Section 2: Cyclic Rotation Averaging and Power-Difference Polynomials -/

def cycPerm (n : ℕ) (hn : 0 < n) : Equiv.Perm (Fin n) where
  toFun i := ⟨(i.1 + 1) % n, Nat.mod_lt _ hn⟩
  invFun i := ⟨(i.1 + n - 1) % n, Nat.mod_lt _ hn⟩
  left_inv i := by
    ext
    dsimp only
    have hi := i.isLt
    by_cases h : i.1 + 1 < n
    · rw [Nat.mod_eq_of_lt h]
      have : i.1 + 1 + n - 1 = i.1 + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    · have heq : i.1 + 1 = n := by omega
      rw [heq, Nat.mod_self]
      have : 0 + n - 1 = i.1 := by omega
      rw [this, Nat.mod_eq_of_lt hi]
  right_inv i := by
    ext
    dsimp only
    have hi := i.isLt
    by_cases h : i.1 = 0
    · rw [h]
      have : 0 + n - 1 = n - 1 := by omega
      rw [this, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
      have : n - 1 + 1 = n := by omega
      rw [this, Nat.mod_self]
    · have : i.1 + n - 1 = i.1 - 1 + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i.1 - 1 < n)]
      have : i.1 - 1 + 1 = i.1 := by omega
      rw [this, Nat.mod_eq_of_lt hi]

lemma root_cycPerm {n : ℕ} (hn : 0 < n) (i : Fin n) :
    root n (cycPerm n hn i) = zeta n * root n i := by
  unfold root cycPerm
  dsimp
  have hi := i.isLt
  by_cases h : i.1 + 1 < n
  · rw [Nat.mod_eq_of_lt h, pow_succ']
  · have heq : i.1 + 1 = n := by omega
    rw [heq, Nat.mod_self, pow_zero, ← pow_succ', heq, (isPrimitiveRoot_zeta hn).pow_eq_one]

lemma sum_perm_pow_eq_zero {n m : ℕ} (hn : 0 < n) (hm0 : 0 < m) (hmn : m < n)
    (π : Equiv.Perm (Fin n)) (w : Fin n → ℂ) :
    ∑ σ : Equiv.Perm (Fin n), (∑ j : Fin n, w j * root n (π (σ j))) ^ m = 0 := by
  set T := ∑ σ : Equiv.Perm (Fin n), (∑ j : Fin n, w j * root n (π (σ j))) ^ m
  set rot : Equiv.Perm (Fin n) := π.symm * cycPerm n hn * π
  have hrot : ∀ i : Fin n, root n (π (rot i)) = zeta n * root n (π i) := by
    intro i
    simp [rot, Equiv.Perm.mul_apply, root_cycPerm hn]
  have hT : T = (zeta n) ^ m * T := by
    calc T = ∑ σ : Equiv.Perm (Fin n),
              (∑ j : Fin n, w j * root n (π ((rot * σ) j))) ^ m := by
            simpa using (Equiv.sum_comp (Equiv.mulLeft rot)
              (fun σ => (∑ j : Fin n, w j * root n (π (σ j))) ^ m)).symm
      _ = ∑ σ : Equiv.Perm (Fin n),
            (zeta n * ∑ j : Fin n, w j * root n (π (σ j))) ^ m := by
          refine Finset.sum_congr rfl (fun σ _ => ?_)
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Equiv.Perm.mul_apply, hrot (σ j)]
          ring
      _ = (zeta n) ^ m * T := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun σ _ => mul_pow _ _ _)
  have hne1 : (zeta n) ^ m ≠ 1 :=
    (isPrimitiveRoot_zeta hn).pow_ne_one_of_pos_of_lt hm0.ne' hmn
  have hsub : (1 - (zeta n) ^ m) * T = 0 := by linear_combination hT
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne1.symm)

lemma sum_perm_sub_pow {n r : ℕ} (hn : 0 < n) (hr : r < n)
    (π : Equiv.Perm (Fin n)) (c₀ : ℂ) (w : Fin n → ℂ) :
    ∑ σ : Equiv.Perm (Fin n), (c₀ - ∑ j : Fin n, w j * root n (π (σ j))) ^ r =
      (Fintype.card (Equiv.Perm (Fin n)) : ℂ) * c₀ ^ r := by
  have hexp : ∀ σ : Equiv.Perm (Fin n),
      (c₀ - ∑ j : Fin n, w j * root n (π (σ j))) ^ r =
        ∑ m ∈ Finset.range (r + 1),
          ((-1 : ℂ) ^ m * (r.choose m : ℂ) * c₀ ^ (r - m)) *
            (∑ j : Fin n, w j * root n (π (σ j))) ^ m := by
    intro σ
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [neg_eq_neg_one_mul, mul_pow]
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm, Finset.sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  suffices hrest : ∑ k ∈ Finset.range r,
      ∑ x : Equiv.Perm (Fin n),
        (-1 : ℂ) ^ (k + 1) * (r.choose (k + 1) : ℂ) * c₀ ^ (r - (k + 1)) *
          (∑ j : Fin n, w j * root n (π (x j))) ^ (k + 1) = 0 by
    rw [hrest, zero_add]
  refine Finset.sum_eq_zero (fun k hk => ?_)
  rw [← Finset.mul_sum]
  rw [sum_perm_pow_eq_zero hn (by omega) (by rw [Finset.mem_range] at hk; omega) π w, mul_zero]

/-! ### Finite-Difference Operator on `Polynomial ℂ` -/

def diffOp (t : ℂ) : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ where
  toFun P := P - P.comp (Polynomial.X + Polynomial.C t)
  map_add' P Q := by
    rw [Polynomial.add_comp]
    abel
  map_smul' c P := by
    rw [Polynomial.smul_comp, RingHom.id_apply, smul_sub]

lemma eval_diffOp (t x : ℂ) (P : Polynomial ℂ) :
    (diffOp t P).eval x = P.eval x - P.eval (x + t) := by
  simp [diffOp]

lemma diffOp_C (t c : ℂ) : diffOp t (Polynomial.C c) = 0 := by
  simp [diffOp]

def degLT (k : ℕ) (P : Polynomial ℂ) : Prop :=
  ∀ m : ℕ, k ≤ m → P.coeff m = 0

lemma eq_zero_of_degLT_zero {P : Polynomial ℂ} (hP : degLT 0 P) : P = 0 := by
  ext m
  simpa using hP m (Nat.zero_le m)

lemma degLT_add {k : ℕ} {P Q : Polynomial ℂ} (hP : degLT k P) (hQ : degLT k Q) :
    degLT k (P + Q) := fun m hm => by
  rw [Polynomial.coeff_add, hP m hm, hQ m hm, add_zero]

lemma degLT_sub {k : ℕ} {P Q : Polynomial ℂ} (hP : degLT k P) (hQ : degLT k Q) :
    degLT k (P - Q) := fun m hm => by
  rw [Polynomial.coeff_sub, hP m hm, hQ m hm, sub_zero]

lemma degLT_smul {k : ℕ} (c : ℂ) {P : Polynomial ℂ} (hP : degLT k P) :
    degLT k (c • P) := fun m hm => by
  rw [Polynomial.coeff_smul, hP m hm, smul_eq_mul, mul_zero]

lemma degLT_mono {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) {P : Polynomial ℂ} (hP : degLT k₁ P) :
    degLT k₂ P := fun m hm => hP m (le_trans hle hm)

lemma degLT_diffOp_X_pow_add (k : ℕ) (t : ℂ) :
    degLT k (diffOp t (Polynomial.X ^ (k + 1)) +
      Polynomial.C (((k + 1 : ℕ) : ℂ) * t) * Polynomial.X ^ k) := by
  have hexp : (Polynomial.X + Polynomial.C t) ^ (k + 1) =
      ∑ j ∈ Finset.range (k + 2),
        Polynomial.C (t ^ (k + 1 - j) * ((k + 1).choose j : ℂ)) * Polynomial.X ^ j := by
    rw [add_pow]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Polynomial.C_eq_natCast, ← Polynomial.C_pow,
      show Polynomial.X ^ j * Polynomial.C (t ^ (k + 1 - j)) * Polynomial.C ↑((k + 1).choose j) =
        (Polynomial.C (t ^ (k + 1 - j)) * Polynomial.C ((k + 1).choose j : ℂ)) * Polynomial.X ^ j
        by ring,
      ← Polynomial.C_mul]
  have hsplit : diffOp t (Polynomial.X ^ (k + 1)) +
      Polynomial.C (((k + 1 : ℕ) : ℂ) * t) * Polynomial.X ^ k =
      - ∑ j ∈ Finset.range k,
          Polynomial.C (t ^ (k + 1 - j) * ((k + 1).choose j : ℂ)) * Polynomial.X ^ j := by
    simp only [diffOp, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.X_pow_comp]
    rw [hexp, Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : k + 1 - (k + 1) = 0 := by omega
    have h2 : k + 1 - k = 1 := by omega
    rw [h1, h2, Nat.choose_self, Nat.choose_succ_self_right]
    push_cast
    simp only [pow_zero, pow_one, one_mul, Polynomial.C_1, Polynomial.C_mul, Polynomial.C_add]
    ring
  rw [hsplit]
  intro m hm
  rw [Polynomial.coeff_neg, Polynomial.finsetSum_coeff]
  suffices hsum : ∑ j ∈ Finset.range k,
      (Polynomial.C (t ^ (k + 1 - j) * ((k + 1).choose j : ℂ)) * Polynomial.X ^ j).coeff m = 0 by
    rw [hsum, neg_zero]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega : m ≠ j), mul_zero]

lemma degLT_diffOp {k : ℕ} (t : ℂ) {P : Polynomial ℂ} (hP : degLT (k + 1) P) :
    degLT k (diffOp t P) := by
  induction k generalizing P with
  | zero =>
    have hC : P = Polynomial.C (P.coeff 0) := by
      ext m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · rw [hP m hm, Polynomial.coeff_C, if_neg (by omega : m ≠ 0)]
    rw [hC, diffOp_C]
    intro m _; simp
  | succ k ih =>
    set P_low := P - Polynomial.C (P.coeff (k + 1)) * Polynomial.X ^ (k + 1)
    have hP_eq : P = P_low + (P.coeff (k + 1)) • Polynomial.X ^ (k + 1) := by
      rw [Polynomial.smul_eq_C_mul]
      dsimp [P_low]
      ring
    have hlow : degLT (k + 1) P_low := by
      intro m hm
      dsimp [P_low]
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hmk : m = k + 1
      · subst hmk; simp
      · rw [if_neg hmk, mul_zero, sub_zero]
        exact hP m (by omega)
    set R := diffOp t (Polynomial.X ^ (k + 1)) +
      Polynomial.C (((k + 1 : ℕ) : ℂ) * t) * Polynomial.X ^ k
    have hR : degLT k R := degLT_diffOp_X_pow_add k t
    have htop : degLT (k + 1) (diffOp t (Polynomial.X ^ (k + 1))) := by
      have hexpr : diffOp t (Polynomial.X ^ (k + 1)) =
          R - Polynomial.C (((k + 1 : ℕ) : ℂ) * t) * Polynomial.X ^ k := eq_sub_of_add_eq rfl
      rw [hexpr]
      refine degLT_sub (degLT_mono (by omega) hR) (fun m hm => ?_)
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega : m ≠ k), mul_zero]
    rw [hP_eq, map_add, LinearMap.map_smul]
    exact degLT_add (degLT_mono (by omega) (ih hlow)) (degLT_smul _ htop)

def iterDiff : List ℂ → (Polynomial ℂ →ₗ[ℂ] Polynomial ℂ)
  | [] => LinearMap.id
  | t :: ts => (iterDiff ts).comp (diffOp t)

lemma iterDiff_eq_zero_of_degLT (ts : List ℂ) {P : Polynomial ℂ}
    (hP : degLT ts.length P) :
    iterDiff ts P = 0 := by
  induction ts generalizing P with
  | nil => exact eq_zero_of_degLT_zero hP
  | cons t ts ih => exact ih (degLT_diffOp t hP)

lemma iterDiff_X_pow (ts : List ℂ) :
    iterDiff ts (Polynomial.X ^ ts.length) =
      Polynomial.C ((-1 : ℂ) ^ ts.length * (ts.length.factorial : ℂ) * ts.prod) := by
  induction ts with
  | nil =>
    simp [iterDiff]
  | cons t ts ih =>
    set k := ts.length
    simp only [List.length_cons, iterDiff, LinearMap.comp_apply]
    set R := diffOp t (Polynomial.X ^ (k + 1)) +
      Polynomial.C (((k + 1 : ℕ) : ℂ) * t) * Polynomial.X ^ k
    have hR : degLT k R := degLT_diffOp_X_pow_add k t
    have hexpr : diffOp t (Polynomial.X ^ (k + 1)) =
        R + ((- (((k + 1 : ℕ) : ℂ) * t)) • Polynomial.X ^ k) := by
      rw [Polynomial.smul_eq_C_mul, map_neg]
      dsimp [R]
      ring
    rw [hexpr, map_add, iterDiff_eq_zero_of_degLT ts hR, zero_add,
      LinearMap.map_smul, ih, Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
    congr 1
    rw [List.prod_cons, Nat.factorial_succ, pow_succ]
    push_cast
    ring

/-! ### Section 3: `ZaPoly`, Ideals `J_τ`, and Power-Sum Vanishing -/

abbrev APoly (n : ℕ) := MvPolynomial (Fin n) ℤ
abbrev ZaPoly (n : ℕ) := MvPolynomial (Fin n) (APoly n)
abbrev ZaSeries (n : ℕ) := MvPowerSeries (Fin n) (APoly n)

def Z_var {n : ℕ} (i : Fin n) : ZaPoly n := MvPolynomial.X i
def A_var {n : ℕ} (j : Fin n) : ZaPoly n := MvPolynomial.C (MvPolynomial.X j)

def JIdeal {n : ℕ} (τ : Equiv.Perm (Fin n)) : Ideal (ZaPoly n) :=
  Ideal.span (Set.range (fun i : Fin n => 1 - Z_var i * A_var (τ i)))

def evalAOne (n : ℕ) : ZaPoly n →+* MvPolynomial (Fin n) ℤ :=
  MvPolynomial.map (MvPolynomial.eval (fun _ => (1 : ℤ)))

def evalPow {n : ℕ} (y : Fin n → ℂ) (r : ℕ) : MvPolynomial (Fin n) ℤ →+ ℂ :=
  AddMonoidAlgebra.liftNC (Int.castAddHom ℂ) (fun u => (∑ i : Fin n, (u i : ℂ) * y i) ^ r)

lemma evalPow_monomial {n : ℕ} (y : Fin n → ℂ) (r : ℕ) (u : Fin n →₀ ℕ) (c : ℤ) :
    evalPow y r (MvPolynomial.monomial u c) = (c : ℂ) * (∑ i : Fin n, (u i : ℂ) * y i) ^ r := by
  unfold evalPow
  exact AddMonoidAlgebra.liftNC_single _ _ u c

abbrev GrpAlg (n : ℕ) := AddMonoidAlgebra ℤ (Fin n → ℤ)

def psiA {n : ℕ} (τ : Equiv.Perm (Fin n)) : APoly n →+* GrpAlg n :=
  MvPolynomial.eval₂Hom (Int.castRingHom (GrpAlg n))
    (fun j => AddMonoidAlgebra.single (- (Pi.single (τ.symm j) (1 : ℤ) : Fin n → ℤ)) 1)

def psi {n : ℕ} (τ : Equiv.Perm (Fin n)) : ZaPoly n →+* GrpAlg n :=
  MvPolynomial.eval₂Hom (psiA τ)
    (fun i => AddMonoidAlgebra.single (Pi.single i (1 : ℤ) : Fin n → ℤ) 1)

lemma psi_eq_zero_of_mem_JIdeal {n : ℕ} (τ : Equiv.Perm (Fin n)) {Q : ZaPoly n}
    (hQ : Q ∈ JIdeal τ) : psi τ Q = 0 := by
  rw [← RingHom.mem_ker]
  refine Ideal.span_le.mpr ?_ hQ
  rintro _ ⟨i, rfl⟩
  simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, map_mul]
  have hZ : psi τ (Z_var i) = AddMonoidAlgebra.single (Pi.single i (1 : ℤ) : Fin n → ℤ) 1 := by
    simp [psi, Z_var]
  have hA : psi τ (A_var (τ i)) =
      AddMonoidAlgebra.single (- (Pi.single i (1 : ℤ) : Fin n → ℤ)) 1 := by
    simp [psi, psiA, A_var]
  rw [hZ, hA, AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]
  exact sub_self 1

def grpEvalPow {n : ℕ} (y : Fin n → ℂ) (r : ℕ) : GrpAlg n →+ ℂ :=
  AddMonoidAlgebra.liftNC (Int.castAddHom ℂ) (fun v => (∑ i : Fin n, (v i : ℂ) * y i) ^ r)

lemma psiA_monomial {n : ℕ} (τ : Equiv.Perm (Fin n)) (w : Fin n →₀ ℕ) (c : ℤ) :
    psiA τ (MvPolynomial.monomial w c) =
      AddMonoidAlgebra.single (fun i => - (w (τ i) : ℤ)) c := by
  unfold psiA
  rw [MvPolynomial.eval₂Hom_monomial]
  have hprod : (w.prod fun j k =>
      (AddMonoidAlgebra.single (-(Pi.single (τ.symm j) (1 : ℤ) : Fin n → ℤ)) (1 : ℤ)) ^ k) =
        AddMonoidAlgebra.single (fun i => - (w (τ i) : ℤ)) 1 := by
    have hpow : ∀ (j : Fin n) (k : ℕ),
        (AddMonoidAlgebra.single (-(Pi.single (τ.symm j) (1 : ℤ) : Fin n → ℤ)) (1 : ℤ)) ^ k =
          AddMonoidAlgebra.single (-(k : ℤ) • (Pi.single (τ.symm j) (1 : ℤ) : Fin n → ℤ)) 1 := by
      intro j k
      induction k with
      | zero => simp; rfl
      | succ k ih =>
        rw [pow_succ, ih, AddMonoidAlgebra.single_mul_single, mul_one]
        congr 1
        ext i
        simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        split_ifs <;> push_cast <;> ring
    rw [Finsupp.prod]
    have hstep : ∀ S : Finset (Fin n),
        ∏ j ∈ S, (AddMonoidAlgebra.single
            (-(Pi.single (τ.symm j) (1 : ℤ) : Fin n → ℤ)) (1 : ℤ)) ^ (w j) =
          AddMonoidAlgebra.single
            (∑ j ∈ S, -(w j : ℤ) • (Pi.single (τ.symm j) (1 : ℤ) : Fin n → ℤ)) 1 := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp; rfl
      | insert j₀ S hj₀ ih =>
        rw [Finset.prod_insert hj₀, Finset.sum_insert hj₀, ih, hpow,
          AddMonoidAlgebra.single_mul_single, mul_one]
    rw [hstep]
    congr 1
    ext i
    rw [Finset.sum_apply]
    have hsup : ∑ x ∈ w.support, (-(w x : ℤ) • (Pi.single (τ.symm x) (1 : ℤ) : Fin n → ℤ)) i =
        ∑ x : Fin n, (-(w x : ℤ) • (Pi.single (τ.symm x) (1 : ℤ) : Fin n → ℤ)) i := by
      refine Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_)
      rw [Finsupp.notMem_support_iff.mp hx]
      simp
    rw [hsup]
    have hbij := Equiv.sum_comp τ
      (fun x => (-(w x : ℤ) • (Pi.single (τ.symm x) (1 : ℤ) : Fin n → ℤ)) i)
    rw [← hbij]
    simp [Pi.single_apply]
  rw [hprod]
  change (AddMonoidAlgebra.single (0 : Fin n → ℤ) c) *
    AddMonoidAlgebra.single (fun i => - (w (τ i) : ℤ)) 1 = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

lemma psi_monomial_monomial {n : ℕ} (τ : Equiv.Perm (Fin n))
    (u w : Fin n →₀ ℕ) (c : ℤ) :
    psi τ (MvPolynomial.monomial u (MvPolynomial.monomial w c)) =
      AddMonoidAlgebra.single (fun i => (u i : ℤ) - (w (τ i) : ℤ)) c := by
  unfold psi
  rw [MvPolynomial.eval₂Hom_monomial, psiA_monomial]
  have hpow : ∀ (i : Fin n) (k : ℕ),
      (AddMonoidAlgebra.single (Pi.single i (1 : ℤ) : Fin n → ℤ) (1 : ℤ)) ^ k =
        AddMonoidAlgebra.single ((k : ℤ) • (Pi.single i (1 : ℤ) : Fin n → ℤ)) 1 := by
    intro i k
    induction k with
    | zero => simp; rfl
    | succ k ih =>
      rw [pow_succ, ih, AddMonoidAlgebra.single_mul_single, mul_one]
      congr 1
      ext m
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs <;> push_cast <;> ring
  have hstep : ∀ S : Finset (Fin n),
      ∏ i ∈ S, (AddMonoidAlgebra.single (Pi.single i (1 : ℤ) : Fin n → ℤ) (1 : ℤ)) ^ (u i) =
        AddMonoidAlgebra.single (∑ i ∈ S, (u i : ℤ) • (Pi.single i (1 : ℤ) : Fin n → ℤ)) 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp; rfl
    | insert i₀ S hi₀ ih =>
      rw [Finset.prod_insert hi₀, Finset.sum_insert hi₀, ih, hpow,
        AddMonoidAlgebra.single_mul_single, mul_one]
  rw [Finsupp.prod, hstep, AddMonoidAlgebra.single_mul_single, mul_one]
  congr 1
  ext i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hsup : ∑ x ∈ u.support, (u x : ℤ) * (Pi.single x (1 : ℤ) : Fin n → ℤ) i =
      ∑ x : Fin n, (u x : ℤ) * (Pi.single x (1 : ℤ) : Fin n → ℤ) i := by
    refine Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_)
    rw [Finsupp.notMem_support_iff.mp hx]; simp
  rw [hsup]
  simp [Pi.single_apply]
  ring

def aEvalShift {n : ℕ} (π σ : Equiv.Perm (Fin n)) (r : ℕ) (c₀ : ℂ) : APoly n →+ ℂ :=
  AddMonoidAlgebra.liftNC (Int.castAddHom ℂ)
    (fun w => (c₀ - ∑ j : Fin n, (w j : ℂ) * root n (π (σ j))) ^ r)

def zaEvalShift {n : ℕ} (π σ : Equiv.Perm (Fin n)) (r : ℕ) : ZaPoly n →+ ℂ where
  toFun P := ∑ u ∈ P.support,
    aEvalShift π σ r (∑ i : Fin n, (u i : ℂ) * root n (π i)) (MvPolynomial.coeff u P)
  map_zero' := by simp
  map_add' P₁ P₂ := by
    have hsub₁ : P₁.support ⊆ P₁.support ∪ P₂.support := Finset.subset_union_left
    have hsub₂ : P₂.support ⊆ P₁.support ∪ P₂.support := Finset.subset_union_right
    have hsub : (P₁ + P₂).support ⊆ P₁.support ∪ P₂.support := MvPolynomial.support_add
    rw [Finset.sum_subset hsub (fun u _ hu => by
        rw [MvPolynomial.notMem_support_iff.mp hu, map_zero]),
      Finset.sum_subset hsub₁ (fun u _ hu => by
        rw [MvPolynomial.notMem_support_iff.mp hu, map_zero]),
      Finset.sum_subset hsub₂ (fun u _ hu => by
        rw [MvPolynomial.notMem_support_iff.mp hu, map_zero]),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [MvPolynomial.coeff_add, map_add]

lemma zaEvalShift_monomial {n : ℕ} (π σ : Equiv.Perm (Fin n)) (r : ℕ)
    (u w : Fin n →₀ ℕ) (c : ℤ) :
    zaEvalShift π σ r (MvPolynomial.monomial u (MvPolynomial.monomial w c)) =
      (c : ℂ) * ((∑ i : Fin n, (u i : ℂ) * root n (π i)) -
        (∑ j : Fin n, (w j : ℂ) * root n (π (σ j)))) ^ r := by
  unfold zaEvalShift
  dsimp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_subset MvPolynomial.support_monomial_subset
      (fun u' _ hu' => by rw [MvPolynomial.notMem_support_iff.mp hu', map_zero]),
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]
  exact AddMonoidAlgebra.liftNC_single _ _ w c

lemma evalPow_evalAOne_eq_zero {n r : ℕ} (hn : 0 < n) (hr : r < n)
    (π : Equiv.Perm (Fin n)) {Q : ZaPoly n}
    (hQ : ∀ τ : Equiv.Perm (Fin n), Q ∈ JIdeal τ) :
    evalPow (fun i => root n (π i)) r (evalAOne n Q) = 0 := by
  set y : Fin n → ℂ := fun i => root n (π i)
  have hτ_id : ∀ τ : Equiv.Perm (Fin n), ∀ P : ZaPoly n,
      grpEvalPow y r (psi τ P) = zaEvalShift π τ.symm r P := by
    intro τ P
    induction P using MvPolynomial.induction_on' with
    | monomial u pA =>
      induction pA using MvPolynomial.induction_on' with
      | monomial w c =>
        rw [zaEvalShift_monomial, psi_monomial_monomial]
        unfold grpEvalPow
        rw [AddMonoidAlgebra.liftNC_single]
        dsimp only [Int.coe_castAddHom]
        congr 2
        have hsub : ∑ i : Fin n, (((u i : ℤ) - (w (τ i) : ℤ) : ℤ) : ℂ) * y i =
            (∑ i : Fin n, (u i : ℂ) * y i) - ∑ i : Fin n, (w (τ i) : ℂ) * y i := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun i _ => by push_cast; ring)
        change ∑ i : Fin n, (((u i : ℤ) - (w (τ i) : ℤ) : ℤ) : ℂ) * y i = _
        rw [hsub]
        congr 1
        simpa [y] using Equiv.sum_comp τ (fun j => (w j : ℂ) * y (τ.symm j))
      | add p₁ p₂ ih₁ ih₂ =>
        rw [map_add (MvPolynomial.monomial u), map_add, map_add, map_add, ih₁, ih₂]
    | add P₁ P₂ ih₁ ih₂ =>
      rw [map_add, map_add, map_add, ih₁, ih₂]
  have hzero_τ : ∀ τ : Equiv.Perm (Fin n), zaEvalShift π τ.symm r Q = 0 := by
    intro τ
    rw [← hτ_id τ Q, psi_eq_zero_of_mem_JIdeal τ (hQ τ), map_zero]
  have hsum_zero : ∑ σ : Equiv.Perm (Fin n), zaEvalShift π σ r Q = 0 := by
    rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))]
    exact Finset.sum_eq_zero (fun τ _ => hzero_τ τ)
  have havg : ∀ P : ZaPoly n,
      ∑ σ : Equiv.Perm (Fin n), zaEvalShift π σ r P =
        (Fintype.card (Equiv.Perm (Fin n)) : ℂ) * evalPow y r (evalAOne n P) := by
    intro P
    induction P using MvPolynomial.induction_on' with
    | monomial u pA =>
      induction pA using MvPolynomial.induction_on' with
      | monomial w c =>
        simp_rw [zaEvalShift_monomial]
        rw [← Finset.mul_sum,
          sum_perm_sub_pow hn hr π (∑ i : Fin n, (u i : ℂ) * y i) (fun j => (w j : ℂ))]
        unfold evalAOne
        rw [MvPolynomial.map_monomial, MvPolynomial.eval_monomial]
        have hprod1 : (w.prod fun _ e => (1 : ℤ) ^ e) = 1 := by
          simp [Finsupp.prod]
        rw [hprod1, mul_one, evalPow_monomial]
        ring
      | add p₁ p₂ ih₁ ih₂ =>
        simp_rw [map_add (MvPolynomial.monomial u), map_add]
        rw [Finset.sum_add_distrib, ih₁, ih₂, mul_add]
    | add P₁ P₂ ih₁ ih₂ =>
      simp_rw [map_add]
      rw [Finset.sum_add_distrib, ih₁, ih₂, mul_add]
  rw [havg Q] at hsum_zero
  have hcard_ne : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (mul_eq_zero.mp hsum_zero).resolve_left hcard_ne

/-! ### Section 4: `ZaFun` Operators and Bigraded Submodules -/

abbrev ZaFun (n : ℕ) := (Fin n →₀ ℕ) → APoly n

def polyToZaFun {n : ℕ} (Q : ZaPoly n) : ZaFun n :=
  fun u => MvPolynomial.coeff u Q

lemma polyToZaFun_inj {n : ℕ} : Function.Injective (@polyToZaFun n) := by
  intro P Q h
  ext u w
  exact MvPolynomial.ext_iff.mp (congrFun h u) w

lemma polyToZaFun_add {n : ℕ} (P Q : ZaPoly n) :
    polyToZaFun (P + Q) = polyToZaFun P + polyToZaFun Q := by
  funext u; exact MvPolynomial.coeff_add u P Q

lemma polyToZaFun_sub {n : ℕ} (P Q : ZaPoly n) :
    polyToZaFun (P - Q) = polyToZaFun P - polyToZaFun Q := by
  funext u; simp [polyToZaFun, MvPolynomial.coeff_sub]

lemma polyToZaFun_zero (n : ℕ) : polyToZaFun (0 : ZaPoly n) = 0 := by
  funext u; exact MvPolynomial.coeff_zero u

def zaShift {n : ℕ} (v : Fin n × Fin n) (F : ZaFun n) : ZaFun n :=
  fun u => if Finsupp.single v.1 1 ≤ u then
    MvPolynomial.X v.2 * F (u - Finsupp.single v.1 1) else 0

lemma zaShift_add {n : ℕ} (v : Fin n × Fin n) (F G : ZaFun n) :
    zaShift v (F + G) = zaShift v F + zaShift v G := by
  funext u; dsimp only [zaShift, Pi.add_apply]; split_ifs <;> simp [mul_add]

lemma zaShift_sub {n : ℕ} (v : Fin n × Fin n) (F G : ZaFun n) :
    zaShift v (F - G) = zaShift v F - zaShift v G := by
  funext u; dsimp only [zaShift, Pi.sub_apply]; split_ifs <;> simp [mul_sub]

lemma zaShift_zero {n : ℕ} (v : Fin n × Fin n) : zaShift v (0 : ZaFun n) = 0 := by
  funext u; dsimp only [zaShift, Pi.zero_apply]; split_ifs <;> simp

lemma single_le_and_single_le_sub_iff {n : ℕ} (i₁ i₂ : Fin n) (u : Fin n →₀ ℕ) :
    (Finsupp.single i₁ 1 ≤ u ∧ Finsupp.single i₂ 1 ≤ u - Finsupp.single i₁ 1) ↔
      Finsupp.single i₁ 1 + Finsupp.single i₂ 1 ≤ u := by
  simp only [Finsupp.le_def, Finsupp.add_apply, Finsupp.tsub_apply]
  constructor
  · rintro ⟨h1, h2⟩ k
    have hk1 := h1 k
    have hk2 := h2 k
    omega
  · intro h
    refine ⟨fun k => ?_, fun k => ?_⟩ <;> specialize h k <;> omega

lemma zaShift_comm {n : ℕ} (v₁ v₂ : Fin n × Fin n) (F : ZaFun n) :
    zaShift v₁ (zaShift v₂ F) = zaShift v₂ (zaShift v₁ F) := by
  funext u
  unfold zaShift
  by_cases h : Finsupp.single v₁.1 1 + Finsupp.single v₂.1 1 ≤ u
  · have h21 : Finsupp.single v₂.1 1 ≤ u ∧
        Finsupp.single v₁.1 1 ≤ u - Finsupp.single v₂.1 1 :=
      (single_le_and_single_le_sub_iff v₂.1 v₁.1 u).mpr (by rwa [add_comm])
    have h12 : Finsupp.single v₁.1 1 ≤ u ∧
        Finsupp.single v₂.1 1 ≤ u - Finsupp.single v₁.1 1 :=
      (single_le_and_single_le_sub_iff v₁.1 v₂.1 u).mpr h
    rw [if_pos h12.1, if_pos h12.2, if_pos h21.1, if_pos h21.2]
    have hsub : u - Finsupp.single v₁.1 1 - Finsupp.single v₂.1 1 =
        u - Finsupp.single v₂.1 1 - Finsupp.single v₁.1 1 := by
      ext k; simp; omega
    rw [hsub, ← mul_assoc, ← mul_assoc, mul_comm (MvPolynomial.X v₁.2)]
  · have h12 : ¬ (Finsupp.single v₁.1 1 ≤ u ∧
        Finsupp.single v₂.1 1 ≤ u - Finsupp.single v₁.1 1) :=
      fun hc => h ((single_le_and_single_le_sub_iff v₁.1 v₂.1 u).mp hc)
    have h21 : ¬ (Finsupp.single v₂.1 1 ≤ u ∧
        Finsupp.single v₁.1 1 ≤ u - Finsupp.single v₂.1 1) :=
      fun hc => h (by rw [add_comm]; exact (single_le_and_single_le_sub_iff v₂.1 v₁.1 u).mp hc)
    by_cases h1 : Finsupp.single v₁.1 1 ≤ u
    · have h2 : ¬ Finsupp.single v₂.1 1 ≤ u - Finsupp.single v₁.1 1 := fun hc => h12 ⟨h1, hc⟩
      rw [if_pos h1, if_neg h2, mul_zero]
      by_cases h1' : Finsupp.single v₂.1 1 ≤ u
      · have h2' : ¬ Finsupp.single v₁.1 1 ≤ u - Finsupp.single v₂.1 1 := fun hc => h21 ⟨h1', hc⟩
        rw [if_pos h1', if_neg h2', mul_zero]
      · rw [if_neg h1']
    · rw [if_neg h1]
      by_cases h1' : Finsupp.single v₂.1 1 ≤ u
      · have h2' : ¬ Finsupp.single v₁.1 1 ≤ u - Finsupp.single v₂.1 1 := fun hc => h21 ⟨h1', hc⟩
        rw [if_pos h1', if_neg h2', mul_zero]
      · rw [if_neg h1']

def mulFactor {n : ℕ} (v : Fin n × Fin n) (F : ZaFun n) : ZaFun n :=
  F - zaShift v F

lemma mulFactor_add {n : ℕ} (v : Fin n × Fin n) (F G : ZaFun n) :
    mulFactor v (F + G) = mulFactor v F + mulFactor v G := by
  unfold mulFactor; rw [zaShift_add]; abel

lemma mulFactor_sub {n : ℕ} (v : Fin n × Fin n) (F G : ZaFun n) :
    mulFactor v (F - G) = mulFactor v F - mulFactor v G := by
  unfold mulFactor; rw [zaShift_sub]; abel

lemma mulFactor_zero {n : ℕ} (v : Fin n × Fin n) : mulFactor v (0 : ZaFun n) = 0 := by
  unfold mulFactor; rw [zaShift_zero, sub_zero]

lemma mulFactor_comm {n : ℕ} (v₁ v₂ : Fin n × Fin n) (F : ZaFun n) :
    mulFactor v₁ (mulFactor v₂ F) = mulFactor v₂ (mulFactor v₁ F) := by
  unfold mulFactor
  rw [zaShift_sub, zaShift_sub, zaShift_comm]
  abel

lemma mulFactor_zaShift_comm {n : ℕ} (v₁ v₂ : Fin n × Fin n) (F : ZaFun n) :
    mulFactor v₁ (zaShift v₂ F) = zaShift v₂ (mulFactor v₁ F) := by
  unfold mulFactor
  rw [zaShift_sub, zaShift_comm]

lemma polyToZaFun_Z_A_mul {n : ℕ} (v : Fin n × Fin n) (Q : ZaPoly n) :
    polyToZaFun (Z_var v.1 * A_var v.2 * Q) = zaShift v (polyToZaFun Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u' pA =>
    have hZA : Z_var v.1 * A_var v.2 * MvPolynomial.monomial u' pA =
        MvPolynomial.monomial (Finsupp.single v.1 1 + u') (MvPolynomial.X v.2 * pA) := by
      unfold Z_var A_var
      have hX : (MvPolynomial.X v.1 : ZaPoly n) = MvPolynomial.monomial (Finsupp.single v.1 1) 1 := by
        ext m; simp [MvPolynomial.coeff_X, MvPolynomial.coeff_monomial, eq_comm]
      have hC : (MvPolynomial.C (MvPolynomial.X v.2) : ZaPoly n) =
          MvPolynomial.monomial 0 (MvPolynomial.X v.2) := by
        ext m; simp [MvPolynomial.coeff_C, eq_comm]
      rw [hX, hC, MvPolynomial.monomial_mul, MvPolynomial.monomial_mul,
        add_zero, one_mul]
    rw [hZA]
    funext u
    unfold polyToZaFun zaShift
    simp only [MvPolynomial.coeff_monomial]
    by_cases hle : Finsupp.single v.1 1 ≤ u
    · rw [if_pos hle]
      by_cases heq : Finsupp.single v.1 1 + u' = u
      · have hsub : u - Finsupp.single v.1 1 = u' := by
          ext k; have := congrArg (fun f : Fin n →₀ ℕ => f k) heq; simp at this ⊢; omega
        rw [if_pos heq, hsub, if_pos rfl]
      · have hsub : u - Finsupp.single v.1 1 ≠ u' := by
          intro hc; apply heq; ext k
          have hk := hle k
          have hck := congrArg (fun f : Fin n →₀ ℕ => f k) hc
          simp at hk hck ⊢; omega
        rw [if_neg heq, if_neg hsub.symm, mul_zero]
    · rw [if_neg hle]
      have hne : Finsupp.single v.1 1 + u' ≠ u := by
        intro hc; apply hle; rw [← hc]; intro k; simp
      rw [if_neg hne]
  | add P₁ P₂ ih₁ ih₂ =>
    rw [mul_add, polyToZaFun_add, polyToZaFun_add, ih₁, ih₂, ← zaShift_add]

lemma polyToZaFun_one_sub_mul {n : ℕ} (v : Fin n × Fin n) (Q : ZaPoly n) :
    polyToZaFun ((1 - Z_var v.1 * A_var v.2) * Q) = mulFactor v (polyToZaFun Q) := by
  rw [sub_mul, one_mul, polyToZaFun_sub, polyToZaFun_Z_A_mul]
  rfl

lemma perm_foldr_eq {α β : Type*} (f : α → β → β)
    (hcomm : ∀ a₁ a₂ b, f a₁ (f a₂ b) = f a₂ (f a₁ b))
    {l₁ l₂ : List α} (hp : l₁.Perm l₂) (b : β) :
    l₁.foldr f b = l₂.foldr f b := by
  induction hp generalizing b with
  | nil => rfl
  | cons a _ ih => exact congrArg (f a) (ih b)
  | swap a₁ a₂ _ => simp only [List.foldr_cons]; exact hcomm a₂ a₁ _
  | trans _ _ ih₁ ih₂ => exact (ih₁ b).trans (ih₂ b)

def prodMulFactor {n : ℕ} (S : Finset (Fin n × Fin n)) (F : ZaFun n) : ZaFun n :=
  S.toList.foldr mulFactor F

lemma prodMulFactor_empty {n : ℕ} (F : ZaFun n) :
    prodMulFactor (∅ : Finset (Fin n × Fin n)) F = F := by
  simp [prodMulFactor]

lemma prodMulFactor_insert {n : ℕ} {v : Fin n × Fin n} {S : Finset (Fin n × Fin n)}
    (hv : v ∉ S) (F : ZaFun n) :
    prodMulFactor (insert v S) F = mulFactor v (prodMulFactor S F) := by
  unfold prodMulFactor
  exact perm_foldr_eq mulFactor mulFactor_comm (Finset.toList_insert hv) F

lemma prodMulFactor_insert_right {n : ℕ} {v : Fin n × Fin n} {S : Finset (Fin n × Fin n)}
    (hv : v ∉ S) (F : ZaFun n) :
    prodMulFactor (insert v S) F = prodMulFactor S (mulFactor v F) := by
  rw [prodMulFactor_insert hv]
  unfold prodMulFactor
  induction S.toList with
  | nil => rfl
  | cons w ws ih => simp only [List.foldr_cons, ← ih, mulFactor_comm]

lemma prodMulFactor_erase {n : ℕ} {v : Fin n × Fin n} {S : Finset (Fin n × Fin n)}
    (hv : v ∈ S) (F : ZaFun n) :
    mulFactor v (prodMulFactor (S.erase v) F) = prodMulFactor S F := by
  conv_rhs => rw [← Finset.insert_erase hv]
  exact (prodMulFactor_insert (Finset.notMem_erase v S) F).symm

lemma prodMulFactor_add {n : ℕ} (S : Finset (Fin n × Fin n)) (F G : ZaFun n) :
    prodMulFactor S (F + G) = prodMulFactor S F + prodMulFactor S G := by
  unfold prodMulFactor
  induction S.toList with
  | nil => rfl
  | cons v vs ih => simp only [List.foldr_cons, ih, mulFactor_add]

lemma prodMulFactor_sub {n : ℕ} (S : Finset (Fin n × Fin n)) (F G : ZaFun n) :
    prodMulFactor S (F - G) = prodMulFactor S F - prodMulFactor S G := by
  unfold prodMulFactor
  induction S.toList with
  | nil => rfl
  | cons v vs ih => simp only [List.foldr_cons, ih, mulFactor_sub]

lemma prodMulFactor_zero {n : ℕ} (S : Finset (Fin n × Fin n)) :
    prodMulFactor S (0 : ZaFun n) = 0 := by
  unfold prodMulFactor
  induction S.toList with
  | nil => rfl
  | cons v vs ih => simp only [List.foldr_cons, ih, mulFactor_zero]

lemma prodMulFactor_zaShift_comm {n : ℕ} (S : Finset (Fin n × Fin n))
    (v : Fin n × Fin n) (F : ZaFun n) :
    prodMulFactor S (zaShift v F) = zaShift v (prodMulFactor S F) := by
  unfold prodMulFactor
  induction S.toList with
  | nil => rfl
  | cons w ws ih => simp only [List.foldr_cons, ih, mulFactor_zaShift_comm]

def evalAOneFun {n : ℕ} (F : ZaFun n) : (Fin n →₀ ℕ) → ℤ :=
  fun u => MvPolynomial.eval (fun _ => (1 : ℤ)) (F u)

lemma evalAOneFun_polyToZaFun {n : ℕ} (Q : ZaPoly n) (u : Fin n →₀ ℕ) :
    evalAOneFun (polyToZaFun Q) u = MvPolynomial.coeff u (evalAOne n Q) := by
  unfold evalAOneFun polyToZaFun evalAOne
  exact (MvPolynomial.coeff_map _ Q u).symm

def rowMulFactor {n : ℕ} (i : Fin n) (g : (Fin n →₀ ℕ) → ℤ) : (Fin n →₀ ℕ) → ℤ :=
  fun u => g u - if Finsupp.single i 1 ≤ u then g (u - Finsupp.single i 1) else 0

def prodRowMulFactor {n : ℕ} (S : Finset (Fin n × Fin n)) (g : (Fin n →₀ ℕ) → ℤ) :
    (Fin n →₀ ℕ) → ℤ :=
  S.toList.foldr (fun v acc => rowMulFactor v.1 acc) g

lemma evalAOneFun_mulFactor {n : ℕ} (v : Fin n × Fin n) (F : ZaFun n) :
    evalAOneFun (mulFactor v F) = rowMulFactor v.1 (evalAOneFun F) := by
  funext u
  dsimp only [evalAOneFun, mulFactor, zaShift, rowMulFactor, Pi.sub_apply]
  rw [map_sub]
  congr 1
  split_ifs with h
  · rw [map_mul, MvPolynomial.eval_X, one_mul]
  · rw [map_zero]

lemma evalAOneFun_prodMulFactor {n : ℕ} (S : Finset (Fin n × Fin n)) (F : ZaFun n) :
    evalAOneFun (prodMulFactor S F) = prodRowMulFactor S (evalAOneFun F) := by
  unfold prodMulFactor prodRowMulFactor
  induction S.toList with
  | nil => rfl
  | cons v vs ih => simp only [List.foldr_cons, evalAOneFun_mulFactor, ih]

lemma prodRowMulFactor_sub {n : ℕ} (S : Finset (Fin n × Fin n))
    (g₁ g₂ : (Fin n →₀ ℕ) → ℤ) :
    prodRowMulFactor S (g₁ - g₂) = prodRowMulFactor S g₁ - prodRowMulFactor S g₂ := by
  unfold prodRowMulFactor
  induction S.toList with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.foldr_cons, ih]
    ext u; unfold rowMulFactor; simp only [Pi.sub_apply]
    split_ifs <;> ring

/-! ### Row/Column Degrees and Bigraded Submodules of `I → P` -/

section Bigraded

variable {K : Type*} [Field K] {n : ℕ}

abbrev MatPoly (K : Type*) [Field K] (n : ℕ) := MvPolynomial (Fin n × Fin n) K

def rowDeg {n : ℕ} (m : (Fin n × Fin n) →₀ ℕ) : Fin n →₀ ℕ :=
  m.mapDomain Prod.fst

def colDeg {n : ℕ} (m : (Fin n × Fin n) →₀ ℕ) : Fin n →₀ ℕ :=
  m.mapDomain Prod.snd

def indDeg {n : ℕ} (T : Finset (Fin n)) : Fin n →₀ ℕ :=
  ∑ i ∈ T, Finsupp.single i 1

def oneDeg (n : ℕ) : Fin n →₀ ℕ := indDeg Finset.univ

lemma indDeg_apply {n : ℕ} (T : Finset (Fin n)) (i : Fin n) :
    indDeg T i = if i ∈ T then 1 else 0 := by
  unfold indDeg
  rw [Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

lemma indDeg_add_sdiff {n : ℕ} (S : Finset (Fin n)) :
    indDeg S + indDeg (Finset.univ \ S) = oneDeg n := by
  ext i
  simp only [Finsupp.add_apply, oneDeg, indDeg_apply, Finset.mem_sdiff, Finset.mem_univ, true_and]
  split_ifs <;> omega

lemma rowDeg_zero : rowDeg (0 : (Fin n × Fin n) →₀ ℕ) = 0 := Finsupp.mapDomain_zero
lemma colDeg_zero : colDeg (0 : (Fin n × Fin n) →₀ ℕ) = 0 := Finsupp.mapDomain_zero

lemma rowDeg_add (m₁ m₂ : (Fin n × Fin n) →₀ ℕ) :
    rowDeg (m₁ + m₂) = rowDeg m₁ + rowDeg m₂ := Finsupp.mapDomain_add

lemma colDeg_add (m₁ m₂ : (Fin n × Fin n) →₀ ℕ) :
    colDeg (m₁ + m₂) = colDeg m₁ + colDeg m₂ := Finsupp.mapDomain_add

lemma rowDeg_single (v : Fin n × Fin n) (e : ℕ) :
    rowDeg (Finsupp.single v e) = Finsupp.single v.1 e := Finsupp.mapDomain_single

lemma colDeg_single (v : Fin n × Fin n) (e : ℕ) :
    colDeg (Finsupp.single v e) = Finsupp.single v.2 e := Finsupp.mapDomain_single

lemma rowDeg_apply (m : (Fin n × Fin n) →₀ ℕ) (i : Fin n) :
    rowDeg m i = m.sum (fun x e => if x.1 = i then e else 0) := by
  unfold rowDeg Finsupp.mapDomain
  rw [Finsupp.sum_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp [Finsupp.single_apply]

lemma colDeg_apply (m : (Fin n × Fin n) →₀ ℕ) (j : Fin n) :
    colDeg m j = m.sum (fun x e => if x.2 = j then e else 0) := by
  unfold colDeg Finsupp.mapDomain
  rw [Finsupp.sum_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp [Finsupp.single_apply]

lemma rowDeg_eq_indDeg_of_setMultilinear {T : Finset (Fin n)} {Q : MatPoly K n}
    (hQ : SetMultCost.IsSetMultilinearOn Prod.fst T Q) {m : (Fin n × Fin n) →₀ ℕ}
    (hm : m ∈ Q.support) : rowDeg m = indDeg T := by
  ext i
  rw [rowDeg_apply, indDeg_apply]
  exact hQ m hm i

lemma sum_rowDeg_eq_sum_colDeg (m : (Fin n × Fin n) →₀ ℕ) :
    ∑ i : Fin n, rowDeg m i = ∑ j : Fin n, colDeg m j := by
  have h1 : ∑ i : Fin n, rowDeg m i = m.sum (fun _ e => e) := by
    simp_rw [rowDeg_apply, Finsupp.sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp
  have h2 : ∑ j : Fin n, colDeg m j = m.sum (fun _ e => e) := by
    simp_rw [colDeg_apply, Finsupp.sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp
  exact h1.trans h2.symm

lemma apply_le_rowDeg (m : (Fin n × Fin n) →₀ ℕ) (v : Fin n × Fin n) :
    m v ≤ rowDeg m v.1 := by
  rw [rowDeg_apply, Finsupp.sum]
  by_cases hv : v ∈ m.support
  · have h := Finset.single_le_sum (f := fun x : Fin n × Fin n => if x.1 = v.1 then m x else 0)
      (fun x _ => Nat.zero_le _) hv
    simpa using h
  · rw [Finsupp.notMem_support_iff.mp hv]
    exact Nat.zero_le _

def filterPoly (pred : ((Fin n × Fin n) →₀ ℕ) → Prop) :
    MatPoly K n →ₗ[K] MatPoly K n where
  toFun f := ∑ m ∈ f.support, if pred m then MvPolynomial.monomial m (MvPolynomial.coeff m f) else 0
  map_add' f g := by
    ext m
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_add]
    have hsub₁ : f.support ⊆ f.support ∪ g.support := Finset.subset_union_left
    have hsub₂ : g.support ⊆ f.support ∪ g.support := Finset.subset_union_right
    have hsub : (f + g).support ⊆ f.support ∪ g.support := MvPolynomial.support_add
    rw [Finset.sum_subset hsub (fun x _ hx => by
        have hx0 := MvPolynomial.notMem_support_iff.mp hx
        rw [MvPolynomial.coeff_add] at hx0
        rw [hx0]; split_ifs <;> simp),
      Finset.sum_subset hsub₁ (fun x _ hx => by
        rw [MvPolynomial.notMem_support_iff.mp hx]; split_ifs <;> simp),
      Finset.sum_subset hsub₂ (fun x _ hx => by
        rw [MvPolynomial.notMem_support_iff.mp hx]; split_ifs <;> simp),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs <;> simp [MvPolynomial.coeff_add]
  map_smul' c f := by
    ext m
    simp only [RingHom.id_apply, MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_sum]
    have hsub : (c • f).support ⊆ f.support := MvPolynomial.support_smul
    rw [Finset.sum_subset hsub (fun x _ hx => by
        have hx0 := MvPolynomial.notMem_support_iff.mp hx
        rw [MvPolynomial.coeff_smul, smul_eq_mul] at hx0
        rw [hx0]; split_ifs <;> simp),
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs <;> simp [MvPolynomial.coeff_smul, smul_eq_mul, mul_ite]

@[simp]
lemma coeff_filterPoly (pred : ((Fin n × Fin n) →₀ ℕ) → Prop)
    (f : MatPoly K n) (m : (Fin n × Fin n) →₀ ℕ) :
    MvPolynomial.coeff m (filterPoly pred f) = if pred m then MvPolynomial.coeff m f else 0 := by
  unfold filterPoly
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [MvPolynomial.coeff_sum]
  by_cases hm : m ∈ f.support
  · rw [Finset.sum_eq_single m]
    · split_ifs <;> simp
    · intro x _ hxm
      split_ifs with hp
      · rw [MvPolynomial.coeff_monomial, if_neg hxm]
      · simp
    · intro hnot; exact False.elim (hnot hm)
  · rw [Finset.sum_eq_zero]
    · rw [MvPolynomial.notMem_support_iff.mp hm, ite_self]
    · intro x hx
      have hxm : x ≠ m := fun h => hm (h ▸ hx)
      split_ifs with hp
      · rw [MvPolynomial.coeff_monomial, if_neg hxm]
      · simp

def proj {I : Type*} (b : I → (Fin n →₀ ℕ)) (u w : Fin n →₀ ℕ) :
    (I → MatPoly K n) →ₗ[K] (I → MatPoly K n) where
  toFun x p := filterPoly (fun m => rowDeg m + b p = u ∧ colDeg m = w) (x p)
  map_add' x y := by ext p m; simp [map_add]
  map_smul' c x := by ext p m; simp [LinearMap.map_smul]

def rowProj {I : Type*} (b : I → (Fin n →₀ ℕ)) (u : Fin n →₀ ℕ) :
    (I → MatPoly K n) →ₗ[K] (I → MatPoly K n) where
  toFun x p := filterPoly (fun m => rowDeg m + b p = u) (x p)
  map_add' x y := by ext p m; simp [map_add]
  map_smul' c x := by ext p m; simp [LinearMap.map_smul]

lemma proj_proj {I : Type*} (b : I → (Fin n →₀ ℕ)) (u w u' w' : Fin n →₀ ℕ)
    (x : I → MatPoly K n) :
    proj b u w (proj b u' w' x) = if u = u' ∧ w = w' then proj b u w x else 0 := by
  ext p m
  by_cases h : u = u' ∧ w = w'
  · rcases h with ⟨rfl, rfl⟩
    rw [if_pos ⟨rfl, rfl⟩]
    simp only [proj, LinearMap.coe_mk, AddHom.coe_mk, coeff_filterPoly]
    split_ifs <;> rfl
  · rw [if_neg h]
    simp only [proj, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, coeff_filterPoly,
      MvPolynomial.coeff_zero]
    split_ifs with h1 h2
    · exfalso; exact h ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩
    · rfl
    · rfl

lemma rowProj_proj {I : Type*} (b : I → (Fin n →₀ ℕ)) (u u' w' : Fin n →₀ ℕ)
    (x : I → MatPoly K n) :
    rowProj b u (proj b u' w' x) = if u = u' then proj b u' w' x else 0 := by
  ext p m
  rcases eq_or_ne u u' with rfl | h
  · rw [if_pos rfl]
    dsimp only [rowProj, proj, LinearMap.coe_mk, AddHom.coe_mk]
    rw [coeff_filterPoly]
    by_cases hr : rowDeg m + b p = u
    · rw [if_pos hr]
    · rw [if_neg hr, coeff_filterPoly, if_neg (fun hc => hr hc.1)]
  · rw [if_neg h]
    dsimp only [rowProj, proj, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    rw [coeff_filterPoly, MvPolynomial.coeff_zero]
    by_cases hr : rowDeg m + b p = u
    · rw [if_pos hr, coeff_filterPoly, if_neg (fun hc => h (hr.symm.trans hc.1))]
    · rw [if_neg hr]

def B_bound {n : ℕ} (u : Fin n →₀ ℕ) : ℕ := (∑ i : Fin n, u i) + 1

def M_fin {n : ℕ} (u : Fin n →₀ ℕ) : Finset ((Fin n × Fin n) →₀ ℕ) :=
  (Finset.univ : Finset ((Fin n × Fin n) → Fin (B_bound u))).image
    (fun g => Finsupp.equivFunOnFinite.symm (fun x => (g x).1))

def M_col {n : ℕ} (u : Fin n →₀ ℕ) : Finset (Fin n →₀ ℕ) :=
  (Finset.univ : Finset (Fin n → Fin (B_bound u))).image
    (fun g => Finsupp.equivFunOnFinite.symm (fun j => (g j).1))

lemma mem_M_fin_of_rowDeg_le {u : Fin n →₀ ℕ} {m : (Fin n × Fin n) →₀ ℕ}
    (hle : rowDeg m ≤ u) : m ∈ M_fin u := by
  unfold M_fin
  rw [Finset.mem_image]
  have hlt : ∀ v : Fin n × Fin n, m v < B_bound u := by
    intro v
    have h1 : m v ≤ rowDeg m v.1 := apply_le_rowDeg m v
    have h2 : rowDeg m v.1 ≤ u v.1 := hle v.1
    have h3 : u v.1 ≤ ∑ i : Fin n, u i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ v.1)
    unfold B_bound; omega
  refine ⟨fun v => ⟨m v, hlt v⟩, Finset.mem_univ _, ?_⟩
  ext v; simp

lemma colDeg_mem_M_col_of_rowDeg_le {u : Fin n →₀ ℕ} {m : (Fin n × Fin n) →₀ ℕ}
    (hle : rowDeg m ≤ u) : colDeg m ∈ M_col u := by
  unfold M_col
  rw [Finset.mem_image]
  have hsum : ∑ j : Fin n, colDeg m j ≤ ∑ i : Fin n, u i := by
    rw [← sum_rowDeg_eq_sum_colDeg]
    exact Finset.sum_le_sum (fun i _ => hle i)
  have hlt : ∀ j : Fin n, colDeg m j < B_bound u := by
    intro j
    have hj : colDeg m j ≤ ∑ j' : Fin n, colDeg m j' :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    unfold B_bound; omega
  refine ⟨fun j => ⟨colDeg m j, hlt j⟩, Finset.mem_univ _, ?_⟩
  ext j; simp

lemma proj_eq_zero_of_notMem_M_col {I : Type*} (b : I → (Fin n →₀ ℕ))
    {u w : Fin n →₀ ℕ} (hw : w ∉ M_col u) (x : I → MatPoly K n) :
    proj b u w x = 0 := by
  ext p m
  simp only [proj, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, coeff_filterPoly,
    MvPolynomial.coeff_zero, ite_eq_right_iff, and_imp]
  intro hrow hcol
  exfalso
  apply hw
  rw [← hcol]
  refine colDeg_mem_M_col_of_rowDeg_le (fun i => ?_)
  have := congrArg (fun f : Fin n →₀ ℕ => f i) hrow
  simp at this; omega

lemma rowProj_eq_sum_proj {I : Type*} (b : I → (Fin n →₀ ℕ))
    (u : Fin n →₀ ℕ) (x : I → MatPoly K n) :
    rowProj b u x = ∑ w ∈ M_col u, proj b u w x := by
  ext p m
  simp only [rowProj, proj, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    MvPolynomial.coeff_sum, coeff_filterPoly]
  by_cases hrow : rowDeg m + b p = u
  · rw [if_pos hrow]
    have hmem : colDeg m ∈ M_col u :=
      colDeg_mem_M_col_of_rowDeg_le (fun i => by
        have := congrArg (fun f : Fin n →₀ ℕ => f i) hrow; simp at this; omega)
    rw [Finset.sum_eq_single (colDeg m)]
    · simp [hrow]
    · intro w _ hne; rw [if_neg (fun h => hne h.2.symm)]
    · intro hnot; exact False.elim (hnot hmem)
  · rw [if_neg hrow]
    exact (Finset.sum_eq_zero (fun w _ => if_neg (fun h => hrow h.1))).symm

lemma finite_of_le_rowProj {I : Type*} [Fintype I] (b : I → (Fin n →₀ ℕ))
    (u : Fin n →₀ ℕ) (W : Submodule K (I → MatPoly K n))
    (hW : W ≤ LinearMap.range (rowProj b u)) : Module.Finite K W := by
  classical
  set G : Finset (I → MatPoly K n) := Finset.univ.biUnion (fun p : I =>
    (M_fin u).image (fun m => Pi.single p (MvPolynomial.monomial m (1 : K))))
  set S_span : Submodule K (I → MatPoly K n) := Submodule.span K (G : Set (I → MatPoly K n))
  have hle_span : LinearMap.range (rowProj b u) ≤ S_span := by
    rintro _ ⟨x, rfl⟩
    have hx_eq : rowProj b u x = ∑ p : I, ∑ m ∈ M_fin u,
        (MvPolynomial.coeff m (rowProj b u x p)) •
          (Pi.single p (MvPolynomial.monomial m (1 : K)) : I → MatPoly K n) := by
      ext p₀ m₀
      simp only [Finset.sum_apply, Pi.smul_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
        smul_eq_mul, Pi.single_apply]
      rw [Finset.sum_eq_single p₀]
      · by_cases hm₀ : m₀ ∈ M_fin u
        · rw [Finset.sum_eq_single m₀]
          · simp
          · intro m' _ hne
            simp [MvPolynomial.coeff_monomial, hne]
          · intro hnot; exact False.elim (hnot hm₀)
        · rw [Finset.sum_eq_zero]
          · simp only [rowProj, LinearMap.coe_mk, AddHom.coe_mk, coeff_filterPoly]
            split_ifs with hr
            · exfalso; apply hm₀
              exact mem_M_fin_of_rowDeg_le (fun i => by
                have := congrArg (fun f : Fin n →₀ ℕ => f i) hr; simp at this; omega)
            · rfl
          · intro m' hm'
            have hne : m' ≠ m₀ := fun h => hm₀ (h ▸ hm')
            simp [MvPolynomial.coeff_monomial, hne]
      · intro p' _ hp'
        rw [Finset.sum_eq_zero]
        intro m' _
        rw [if_neg (Ne.symm hp'), MvPolynomial.coeff_zero, mul_zero]
      · intro hnot; exact False.elim (hnot (Finset.mem_univ p₀))
    rw [hx_eq]
    refine Submodule.sum_mem S_span (fun p _ => Submodule.sum_mem S_span (fun m hm => ?_))
    refine Submodule.smul_mem S_span _ (Submodule.subset_span ?_)
    simp only [G, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨p, m, hm, rfl⟩
  have hWS : W ≤ S_span := le_trans hW hle_span
  have hFinS : Module.Finite K S_span := Module.Finite.span_of_finite K G.finite_toSet
  have hNoeth : IsNoetherian K S_span := inferInstance
  have hfg_comap : (W.comap S_span.subtype).FG := hNoeth.noetherian _
  have hmap_eq : Submodule.map S_span.subtype (W.comap S_span.subtype) = W := by
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_of_le_right hWS]
  exact Module.Finite.iff_fg.mpr (hmap_eq ▸ hfg_comap.map S_span.subtype)

def piece {I : Type*} (b : I → (Fin n →₀ ℕ))
    (U : Submodule (MatPoly K n) (I → MatPoly K n)) (u w : Fin n →₀ ℕ) :
    Submodule K (I → MatPoly K n) :=
  (U.restrictScalars K) ⊓ LinearMap.range (proj b u w)

def rowPiece {I : Type*} (b : I → (Fin n →₀ ℕ))
    (U : Submodule (MatPoly K n) (I → MatPoly K n)) (u : Fin n →₀ ℕ) :
    Submodule K (I → MatPoly K n) :=
  (U.restrictScalars K) ⊓ LinearMap.range (rowProj b u)

lemma range_proj_le_range_rowProj {I : Type*} (b : I → (Fin n →₀ ℕ)) (u w : Fin n →₀ ℕ) :
    LinearMap.range (proj b u w : (I → MatPoly K n) →ₗ[K] _) ≤ LinearMap.range (rowProj b u) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨proj b u w x, by rw [rowProj_proj, if_pos rfl]⟩

instance instFinitePiece {I : Type*} [Fintype I] (b : I → (Fin n →₀ ℕ))
    (U : Submodule (MatPoly K n) (I → MatPoly K n)) (u w : Fin n →₀ ℕ) :
    Module.Finite K (piece b U u w) :=
  finite_of_le_rowProj b u _ (le_trans inf_le_right (range_proj_le_range_rowProj b u w))

instance instFiniteRowPiece {I : Type*} [Fintype I] (b : I → (Fin n →₀ ℕ))
    (U : Submodule (MatPoly K n) (I → MatPoly K n)) (u : Fin n →₀ ℕ) :
    Module.Finite K (rowPiece b U u) :=
  finite_of_le_rowProj b u _ inf_le_right

def IsBigraded {I : Type*} (b : I → (Fin n →₀ ℕ))
    (U : Submodule (MatPoly K n) (I → MatPoly K n)) : Prop :=
  ∀ y ∈ U, ∀ u w, proj b u w y ∈ U

lemma isBigraded_top {I : Type*} (b : I → (Fin n →₀ ℕ)) :
    IsBigraded b (⊤ : Submodule (MatPoly K n) (I → MatPoly K n)) :=
  fun _ _ _ _ => trivial

lemma isBigraded_bot {I : Type*} (b : I → (Fin n →₀ ℕ)) :
    IsBigraded b (⊥ : Submodule (MatPoly K n) (I → MatPoly K n)) := by
  intro y hy u w
  rw [Submodule.mem_bot] at hy ⊢
  rw [hy, map_zero]

lemma isBigraded_sup {I : Type*} (b : I → (Fin n →₀ ℕ))
    {U V : Submodule (MatPoly K n) (I → MatPoly K n)}
    (hU : IsBigraded b U) (hV : IsBigraded b V) :
    IsBigraded b (U ⊔ V) := by
  intro y hy u w
  rcases Submodule.mem_sup.mp hy with ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  rw [map_add]
  exact Submodule.add_mem_sup (hU y₁ hy₁ u w) (hV y₂ hy₂ u w)

def HSeries (K : Type*) [Field K] {I : Type*} [Fintype I] (b : I → (Fin n →₀ ℕ))
    (U V : Submodule (MatPoly K n) (I → MatPoly K n)) : ZaFun n :=
  fun u => ∑ w ∈ M_col u,
    MvPolynomial.monomial w
      ((Module.finrank K (piece b U u w) : ℤ) - (Module.finrank K (piece b V u w) : ℤ))

lemma HSeries_self {I : Type*} [Fintype I] (b : I → (Fin n →₀ ℕ))
    (U : Submodule (MatPoly K n) (I → MatPoly K n)) :
    HSeries K b U U = 0 := by
  funext u; ext w
  unfold HSeries
  simp

lemma HSeries_trans {I : Type*} [Fintype I] (b : I → (Fin n →₀ ℕ))
    (U W V : Submodule (MatPoly K n) (I → MatPoly K n)) :
    HSeries K b U V = HSeries K b U W + HSeries K b W V := by
  funext u; ext w₀
  unfold HSeries
  simp only [Pi.add_apply, MvPolynomial.coeff_add, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  split_ifs <;> ring

/-! ### Multiplication by `X v` and Grassmann Exactness Identity -/

def mulXLin {I : Type*} (v : Fin n × Fin n) :
    (I → MatPoly K n) →ₗ[MatPoly K n] (I → MatPoly K n) where
  toFun x p := MvPolynomial.X v * x p
  map_add' x y := by funext p; simp [mul_add]
  map_smul' f x := by funext p; simp [smul_eq_mul]; ring

lemma mulX_injective {I : Type*} (v : Fin n × Fin n) :
    Function.Injective (mulXLin v : (I → MatPoly K n) → (I → MatPoly K n)) := by
  intro x y h
  funext p
  have hp : MvPolynomial.X v * x p = MvPolynomial.X v * y p := congrFun h p
  exact mul_left_cancel₀ (MvPolynomial.X_ne_zero v) hp

lemma coeff_X_mul_poly (v : Fin n × Fin n) (f : MatPoly K n) (m : (Fin n × Fin n) →₀ ℕ) :
    MvPolynomial.coeff m (MvPolynomial.X v * f) =
      if Finsupp.single v 1 ≤ m then MvPolynomial.coeff (m - Finsupp.single v 1) f else 0 := by
  induction f using MvPolynomial.induction_on' with
  | monomial m' c =>
    have hX : (MvPolynomial.X v : MatPoly K n) = MvPolynomial.monomial (Finsupp.single v 1) 1 := by
      ext m₀; simp [MvPolynomial.coeff_X, eq_comm]
    rw [hX, MvPolynomial.monomial_mul, one_mul]
    simp only [MvPolynomial.coeff_monomial]
    by_cases hle : Finsupp.single v 1 ≤ m
    · rw [if_pos hle]
      by_cases heq : Finsupp.single v 1 + m' = m
      · have hsub : m - Finsupp.single v 1 = m' := by
          ext x; have := congrArg (fun g : _ →₀ ℕ => g x) heq; simp at this ⊢; omega
        rw [if_pos heq, hsub, if_pos rfl]
      · have hsub : m' ≠ m - Finsupp.single v 1 := by
          intro hc; apply heq; ext x
          have hx := hle x
          have hcx := congrArg (fun g : _ →₀ ℕ => g x) hc
          simp at hx hcx ⊢; omega
        rw [if_neg heq, if_neg hsub]
    · rw [if_neg hle]
      have hne : Finsupp.single v 1 + m' ≠ m := by
        intro hc; apply hle; rw [← hc]; intro x; simp
      rw [if_neg hne]
  | add f₁ f₂ ih₁ ih₂ =>
    rw [mul_add, MvPolynomial.coeff_add, ih₁, ih₂]
    split_ifs with h
    · rw [MvPolynomial.coeff_add]
    · simp

lemma proj_mulX {I : Type*} (b : I → (Fin n →₀ ℕ)) (v : Fin n × Fin n)
    (u w : Fin n →₀ ℕ) (x : I → MatPoly K n) :
    proj b u w (mulXLin v x) =
      if Finsupp.single v.1 1 ≤ u ∧ Finsupp.single v.2 1 ≤ w then
        mulXLin v (proj b (u - Finsupp.single v.1 1) (w - Finsupp.single v.2 1) x)
      else 0 := by
  ext p m
  by_cases h : Finsupp.single v.1 1 ≤ u ∧ Finsupp.single v.2 1 ≤ w
  · rw [if_pos h]
    simp only [proj, mulXLin, LinearMap.coe_mk, AddHom.coe_mk, coeff_filterPoly, coeff_X_mul_poly]
    by_cases hm : Finsupp.single v 1 ≤ m
    · have hsplit : m = Finsupp.single v 1 + (m - Finsupp.single v 1) := by
        ext z; have := hm z; simp at this ⊢; omega
      have hr : rowDeg m = Finsupp.single v.1 1 + rowDeg (m - Finsupp.single v 1) := by
        conv_lhs => rw [hsplit]; rw [rowDeg_add, rowDeg_single]
      have hc : colDeg m = Finsupp.single v.2 1 + colDeg (m - Finsupp.single v 1) := by
        conv_lhs => rw [hsplit]; rw [colDeg_add, colDeg_single]
      by_cases hcond : rowDeg m + b p = u ∧ colDeg m = w
      · have hcond' : rowDeg (m - Finsupp.single v 1) + b p = u - Finsupp.single v.1 1 ∧
            colDeg (m - Finsupp.single v 1) = w - Finsupp.single v.2 1 := by
          refine ⟨?_, ?_⟩
          · ext i; have := congrArg (fun g : Fin n →₀ ℕ => g i) hcond.1
            rw [hr] at this; simp at this ⊢; omega
          · ext j; have := congrArg (fun g : Fin n →₀ ℕ => g j) hcond.2
            rw [hc] at this; simp at this ⊢; omega
        rw [if_pos hcond, if_pos hm, if_pos hm, if_pos hcond']
      · have hnot : ¬ (rowDeg (m - Finsupp.single v 1) + b p = u - Finsupp.single v.1 1 ∧
            colDeg (m - Finsupp.single v 1) = w - Finsupp.single v.2 1) := by
          rintro ⟨h1, h2⟩; apply hcond; refine ⟨?_, ?_⟩
          · ext i; have hi := h.1 i; have := congrArg (fun g : Fin n →₀ ℕ => g i) h1
            rw [hr]; simp at hi this ⊢; omega
          · ext j; have hj := h.2 j; have := congrArg (fun g : Fin n →₀ ℕ => g j) h2
            rw [hc]; simp at hj this ⊢; omega
        rw [if_neg hcond, if_pos hm, if_neg hnot]
    · by_cases hcond : rowDeg m + b p = u ∧ colDeg m = w
      · rw [if_pos hcond, if_neg hm, if_neg hm]
      · rw [if_neg hcond, if_neg hm]
  · rw [if_neg h]
    simp only [proj, mulXLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, coeff_filterPoly,
      coeff_X_mul_poly, MvPolynomial.coeff_zero]
    by_cases hcond : rowDeg m + b p = u ∧ colDeg m = w
    · rw [if_pos hcond]
      by_cases hm : Finsupp.single v 1 ≤ m
      · exfalso; apply h
        have hsplit : m = Finsupp.single v 1 + (m - Finsupp.single v 1) := by
          ext z; have := hm z; simp at this ⊢; omega
        have hr : rowDeg m = Finsupp.single v.1 1 + rowDeg (m - Finsupp.single v 1) := by
          conv_lhs => rw [hsplit]; rw [rowDeg_add, rowDeg_single]
        have hc : colDeg m = Finsupp.single v.2 1 + colDeg (m - Finsupp.single v 1) := by
          conv_lhs => rw [hsplit]; rw [colDeg_add, colDeg_single]
        refine ⟨fun i => ?_, fun j => ?_⟩
        · have := congrArg (fun g : Fin n →₀ ℕ => g i) hcond.1
          rw [hr] at this; simp at this ⊢; omega
        · have := congrArg (fun g : Fin n →₀ ℕ => g j) hcond.2
          rw [hc] at this; simp at this ⊢; omega
      · rw [if_neg hm]
    · rw [if_neg hcond]

lemma isBigraded_map_mulX {I : Type*} (b : I → (Fin n →₀ ℕ)) (v : Fin n × Fin n)
    {U : Submodule (MatPoly K n) (I → MatPoly K n)} (hU : IsBigraded b U) :
    IsBigraded b (Submodule.map (mulXLin v) U) := by
  rintro _ ⟨y, hy, rfl⟩ u w
  rw [proj_mulX]
  split_ifs with h
  · exact ⟨_, hU y hy _ _, rfl⟩
  · exact Submodule.zero_mem _

lemma isBigraded_ker_mulX {I : Type*} (b : I → (Fin n →₀ ℕ)) (v : Fin n × Fin n)
    {U V : Submodule (MatPoly K n) (I → MatPoly K n)}
    (hU : IsBigraded b U) (hV : IsBigraded b V) :
    IsBigraded b (U ⊓ Submodule.comap (mulXLin v) V) := by
  intro y hy u w
  refine ⟨hU y hy.1 u w, ?_⟩
  change mulXLin v (proj b u w y) ∈ V
  have hcomm : mulXLin v (proj b u w y) =
      proj b (u + Finsupp.single v.1 1) (w + Finsupp.single v.2 1) (mulXLin v y) := by
    rw [proj_mulX]
    have hle : Finsupp.single v.1 1 ≤ u + Finsupp.single v.1 1 ∧
        Finsupp.single v.2 1 ≤ w + Finsupp.single v.2 1 :=
      ⟨fun i => by simp, fun j => by simp⟩
    rw [if_pos hle]
    have hu : u + Finsupp.single v.1 1 - Finsupp.single v.1 1 = u := by ext i; simp
    have hw : w + Finsupp.single v.2 1 - Finsupp.single v.2 1 = w := by ext j; simp
    rw [hu, hw]
  rw [hcomm]
  exact hV (mulXLin v y) hy.2 _ _

lemma mulFactor_HSeries {I : Type*} [Fintype I] (b : I → (Fin n →₀ ℕ))
    (v : Fin n × Fin n) {U V : Submodule (MatPoly K n) (I → MatPoly K n)}
    (_hVU : V ≤ U) (hU : IsBigraded b U) (hV : IsBigraded b V) :
    mulFactor v (HSeries K b U V) =
      HSeries K b U (V ⊔ Submodule.map (mulXLin v) U) -
        zaShift v (HSeries K b (U ⊓ Submodule.comap (mulXLin v) V) V) := by
  set Wc := V ⊔ Submodule.map (mulXLin v) U
  set Wk := U ⊓ Submodule.comap (mulXLin v) V
  have hIm : IsBigraded b (Submodule.map (mulXLin v) U) := isBigraded_map_mulX b v hU
  funext u; ext w
  have hcoeff_H : ∀ (M₁ M₂ : Submodule (MatPoly K n) (I → MatPoly K n)) (u₀ w₀ : Fin n →₀ ℕ),
      MvPolynomial.coeff w₀ (HSeries K b M₁ M₂ u₀) =
        (Module.finrank K (piece b M₁ u₀ w₀) : ℤ) -
          (Module.finrank K (piece b M₂ u₀ w₀) : ℤ) := by
    intro M₁ M₂ u₀ w₀
    unfold HSeries
    rw [MvPolynomial.coeff_sum]
    by_cases hw₀ : w₀ ∈ M_col u₀
    · rw [Finset.sum_eq_single w₀]
      · simp
      · intro w' _ hne; simp [MvPolynomial.coeff_monomial, hne]
      · intro hnot; exact False.elim (hnot hw₀)
    · rw [Finset.sum_eq_zero (fun w' hw' => by
        have hne : w' ≠ w₀ := fun h => hw₀ (h ▸ hw')
        simp [MvPolynomial.coeff_monomial, hne])]
      have hb₁ : piece b M₁ u₀ w₀ = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨_, y, rfl⟩
        rw [proj_eq_zero_of_notMem_M_col b hw₀ y]; exact Submodule.zero_mem ⊥
      have hb₂ : piece b M₂ u₀ w₀ = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨_, y, rfl⟩
        rw [proj_eq_zero_of_notMem_M_col b hw₀ y]; exact Submodule.zero_mem ⊥
      rw [hb₁, hb₂, finrank_bot, Nat.cast_zero, sub_self]
  have hcoeff_shift : ∀ (G : ZaFun n),
      MvPolynomial.coeff w (zaShift v G u) =
        if Finsupp.single v.1 1 ≤ u ∧ Finsupp.single v.2 1 ≤ w then
          MvPolynomial.coeff (w - Finsupp.single v.2 1) (G (u - Finsupp.single v.1 1))
        else 0 := by
    intro G
    unfold zaShift
    by_cases hu : Finsupp.single v.1 1 ≤ u
    · rw [if_pos hu]
      have hXcoeff : ∀ p : APoly n,
          MvPolynomial.coeff w (MvPolynomial.X v.2 * p) =
            if Finsupp.single v.2 1 ≤ w then
              MvPolynomial.coeff (w - Finsupp.single v.2 1) p else 0 := by
        intro p
        induction p using MvPolynomial.induction_on' with
        | monomial w' c =>
          have hX : (MvPolynomial.X v.2 : APoly n) =
              MvPolynomial.monomial (Finsupp.single v.2 1) 1 := by
            ext w₀; simp [MvPolynomial.coeff_X, eq_comm]
          rw [hX, MvPolynomial.monomial_mul, one_mul]
          simp only [MvPolynomial.coeff_monomial]
          by_cases hw_le : Finsupp.single v.2 1 ≤ w
          · rw [if_pos hw_le]
            by_cases heq : Finsupp.single v.2 1 + w' = w
            · have hsub : w - Finsupp.single v.2 1 = w' := by
                ext j; have := congrArg (fun g : Fin n →₀ ℕ => g j) heq; simp at this ⊢; omega
              rw [if_pos heq, hsub, if_pos rfl]
            · have hsub : w' ≠ w - Finsupp.single v.2 1 := by
                intro hc; apply heq; ext j
                have hj := hw_le j
                have hcj := congrArg (fun g : Fin n →₀ ℕ => g j) hc
                simp at hj hcj ⊢; omega
              rw [if_neg heq, if_neg hsub]
          · rw [if_neg hw_le, if_neg (fun hc => hw_le (by rw [← hc]; intro j; simp))]
        | add p₁ p₂ ih₁ ih₂ =>
          rw [mul_add, MvPolynomial.coeff_add, ih₁, ih₂]
          split_ifs with h
          · rw [MvPolynomial.coeff_add]
          · simp
      rw [hXcoeff]
      by_cases hw_le : Finsupp.single v.2 1 ≤ w
      · rw [if_pos hw_le, if_pos ⟨hu, hw_le⟩]
      · rw [if_neg hw_le, if_neg (fun hc => hw_le hc.2)]
    · rw [if_neg hu, MvPolynomial.coeff_zero, if_neg (fun hc => hu hc.1)]
  simp only [mulFactor, Pi.sub_apply, MvPolynomial.coeff_sub, hcoeff_H, hcoeff_shift]
  have hWc_sup : piece b Wc u w = piece b V u w ⊔ piece b (Submodule.map (mulXLin v) U) u w := by
    apply le_antisymm
    · rintro z ⟨hzWc, x, rfl⟩
      rcases Submodule.mem_sup.mp hzWc with ⟨z₁, hz₁, z₂, hz₂, heq⟩
      have hproj_eq : proj b u w x = proj b u w z₁ + proj b u w z₂ := by
        rw [← map_add, heq, proj_proj, if_pos ⟨rfl, rfl⟩]
      rw [hproj_eq]
      refine Submodule.add_mem_sup ⟨hV z₁ hz₁ u w, z₁, rfl⟩ ⟨hIm z₂ hz₂ u w, z₂, rfl⟩
    · exact sup_le (fun z hz => ⟨Submodule.mem_sup_left hz.1, hz.2⟩)
        (fun z hz => ⟨Submodule.mem_sup_right hz.1, hz.2⟩)
  by_cases hle : Finsupp.single v.1 1 ≤ u ∧ Finsupp.single v.2 1 ≤ w
  · rw [if_pos hle, if_pos hle]
    set u' := u - Finsupp.single v.1 1
    set w' := w - Finsupp.single v.2 1
    set μK : (I → MatPoly K n) →ₗ[K] (I → MatPoly K n) := (mulXLin v).restrictScalars K
    have hinjK : Function.Injective μK := mulX_injective v
    have hB_eq : piece b (Submodule.map (mulXLin v) U) u w =
        Submodule.map μK (piece b U u' w') := by
      apply le_antisymm
      · rintro _ ⟨⟨y, hyU, hy_eq⟩, x, rfl⟩
        have hpx : proj b u w (mulXLin v y) = proj b u w x := by
          rw [hy_eq, proj_proj, if_pos ⟨rfl, rfl⟩]
        rw [← hpx, proj_mulX, if_pos hle]
        exact ⟨proj b u' w' y, ⟨hU y hyU u' w', y, rfl⟩, rfl⟩
      · rintro _ ⟨y, ⟨hyU, x, rfl⟩, rfl⟩
        refine ⟨⟨proj b u' w' x, hyU, rfl⟩, mulXLin v x, ?_⟩
        rw [proj_mulX, if_pos hle]; rfl
    have hInf_eq : piece b V u w ⊓ piece b (Submodule.map (mulXLin v) U) u w =
        Submodule.map μK (piece b Wk u' w') := by
      rw [hB_eq]
      apply le_antisymm
      · rintro _ ⟨⟨hzV, _⟩, ⟨y, ⟨hyU, x, rfl⟩, rfl⟩⟩
        exact ⟨proj b u' w' x, ⟨⟨hyU, hzV⟩, x, rfl⟩, rfl⟩
      · rintro _ ⟨y, ⟨⟨hyU, hyV⟩, x, rfl⟩, rfl⟩
        refine ⟨⟨hyV, mulXLin v x, ?_⟩, ⟨proj b u' w' x, ⟨hyU, x, rfl⟩, rfl⟩⟩
        rw [proj_mulX, if_pos hle]; rfl
    have hfinrank_eq_of_sub_eq : ∀ {A B : Submodule K (I → MatPoly K n)},
        A = B → Module.finrank K A = Module.finrank K B := by
      rintro A B rfl; rfl
    have hdimB : Module.finrank K (piece b (Submodule.map (mulXLin v) U) u w) =
        Module.finrank K (piece b U u' w') := by
      rw [hfinrank_eq_of_sub_eq (hB_eq.trans (LinearMap.range_domRestrict _ _).symm)]
      exact (LinearEquiv.finrank_eq (LinearEquiv.ofInjective (μK.domRestrict _)
        (fun a b hab => Subtype.ext (hinjK hab)))).symm
    have hdimInf : Module.finrank K
        ↥(piece b V u w ⊓ piece b (Submodule.map (mulXLin v) U) u w) =
        Module.finrank K (piece b Wk u' w') := by
      rw [hfinrank_eq_of_sub_eq (hInf_eq.trans (LinearMap.range_domRestrict _ _).symm)]
      exact (LinearEquiv.finrank_eq (LinearEquiv.ofInjective (μK.domRestrict _)
        (fun a b hab => Subtype.ext (hinjK hab)))).symm
    have hgrass := Submodule.finrank_sup_add_finrank_inf_eq
      (piece b V u w) (piece b (Submodule.map (mulXLin v) U) u w)
    rw [← hWc_sup, hdimInf, hdimB] at hgrass
    have hgrassZ : (Module.finrank K (piece b Wc u w) : ℤ) +
        (Module.finrank K (piece b Wk u' w') : ℤ) =
          (Module.finrank K (piece b V u w) : ℤ) +
            (Module.finrank K (piece b U u' w') : ℤ) := by exact_mod_cast hgrass
    linarith
  · rw [if_neg hle, if_neg hle]
    have hB_bot : piece b (Submodule.map (mulXLin v) U) u w = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨⟨y, _, hy_eq⟩, x, rfl⟩
      have hpx : proj b u w (mulXLin v y) = proj b u w x := by
        rw [hy_eq, proj_proj, if_pos ⟨rfl, rfl⟩]
      rw [← hpx, proj_mulX, if_neg hle]
      exact Submodule.zero_mem ⊥
    rw [hWc_sup, hB_bot, sup_bot_eq]

/-! ### Lexicographic Column Filtration and Dimension Telescoping -/

def colLexEquiv (n : ℕ) : (Fin n →₀ ℕ) ≃ Lex (Fin n → ℕ) :=
  Finsupp.equivFunOnFinite.trans toLex

lemma colLex_add_lt_iff {n : ℕ} (w₁ w₂ w : Fin n →₀ ℕ) :
    colLexEquiv n (w₁ + w) < colLexEquiv n (w₂ + w) ↔
      colLexEquiv n w₁ < colLexEquiv n w₂ := by
  change (∃ j, (∀ j' < j, (w₁ + w) j' = (w₂ + w) j') ∧ (w₁ + w) j < (w₂ + w) j) ↔
    (∃ j, (∀ j' < j, w₁ j' = w₂ j') ∧ w₁ j < w₂ j)
  simp only [Finsupp.add_apply]
  exact ⟨fun ⟨j, heq, hlt⟩ => ⟨j, fun j' hj' => by specialize heq j' hj'; omega, by omega⟩,
    fun ⟨j, heq, hlt⟩ => ⟨j, fun j' hj' => by rw [heq j' hj'], by omega⟩⟩

def filtLe {I : Type*} (b : I → (Fin n →₀ ℕ)) (u : Fin n →₀ ℕ)
    (V : Submodule K (I → MatPoly K n)) (w : Fin n →₀ ℕ) :
    Submodule K (I → MatPoly K n) where
  carrier := { h ∈ V | ∀ w', colLexEquiv n w < colLexEquiv n w' → proj b u w' h = 0 }
  zero_mem' := ⟨V.zero_mem, fun _ _ => map_zero _⟩
  add_mem' ha hb := ⟨V.add_mem ha.1 hb.1, fun w' hw' => by rw [map_add, ha.2 w' hw', hb.2 w' hw', add_zero]⟩
  smul_mem' c _ ha := ⟨V.smul_mem c ha.1, fun w' hw' => by rw [LinearMap.map_smul, ha.2 w' hw', smul_zero]⟩

def initSub {I : Type*} (b : I → (Fin n →₀ ℕ)) (u : Fin n →₀ ℕ)
    (V : Submodule K (I → MatPoly K n)) (w : Fin n →₀ ℕ) :
    Submodule K (I → MatPoly K n) :=
  Submodule.map (proj b u w) (filtLe b u V w)

lemma sum_finrank_initSub_aux {I : Type*} [Fintype I] (b : I → (Fin n →₀ ℕ))
    (u : Fin n →₀ ℕ) :
    ∀ (m : ℕ) (S : Finset (Fin n →₀ ℕ)), S.card = m →
      ∀ (V : Submodule K (I → MatPoly K n)),
        V ≤ LinearMap.range (rowProj b u) →
        (∀ h ∈ V, ∀ w ∉ S, proj b u w h = 0) →
        ∑ w ∈ S, Module.finrank K (initSub b u V w) = Module.finrank K V := by
  intro m
  induction m with
  | zero =>
    intro S hScard V hVrow hVsupp
    have hS0 : S = ∅ := Finset.card_eq_zero.mp hScard
    subst hS0
    rw [Finset.sum_empty]
    have hVbot : V = ⊥ := by
      rw [eq_bot_iff]
      intro h hh
      rcases hVrow hh with ⟨x, hx⟩
      have hrow : rowProj b u h = h := by
        rw [← hx, rowProj, LinearMap.coe_mk, AddHom.coe_mk]
        ext p m₀; simp only [coeff_filterPoly]; split_ifs <;> rfl
      rw [← hrow, rowProj_eq_sum_proj]
      have h0 : ∑ w ∈ M_col u, proj b u w h = 0 :=
        Finset.sum_eq_zero (fun w _ => hVsupp h hh w (Finset.notMem_empty w))
      rw [h0]; exact Submodule.zero_mem ⊥
    rw [hVbot, finrank_bot]
  | succ m ih =>
    intro S hScard V hVrow hVsupp
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨w₀, hw₀S, hw₀max⟩ := S.exists_max_image (colLexEquiv n) hSne
    have hVfin : Module.Finite K V := finite_of_le_rowProj b u V hVrow
    have hfilt_top : filtLe b u V w₀ = V := by
      apply le_antisymm (fun _ hh => hh.1)
      intro h hh
      refine ⟨hh, fun w' hw' => hVsupp h hh w' (fun hw'S => ?_)⟩
      exact not_le_of_gt hw' (hw₀max w' hw'S)
    set φ : V →ₗ[K] (I → MatPoly K n) := (proj b u w₀).domRestrict V
    have hrange_eq : LinearMap.range φ = initSub b u V w₀ := by
      unfold initSub
      rw [hfilt_top]
      ext z
      simp [φ]
    set V' : Submodule K (I → MatPoly K n) :=
      LinearMap.range (V.subtype.domRestrict (LinearMap.ker φ))
    have hV'_mem : ∀ z, z ∈ V' ↔ z ∈ V ∧ proj b u w₀ z = 0 := by
      intro z
      simp only [V', LinearMap.mem_range, LinearMap.domRestrict_apply, Submodule.coe_subtype]
      exact ⟨fun ⟨⟨⟨y, hy⟩, hker⟩, hyz⟩ =>
          ⟨hyz ▸ hy, hyz ▸ LinearMap.mem_ker.mp hker⟩,
        fun ⟨hz, h0⟩ => ⟨⟨⟨z, hz⟩, h0⟩, rfl⟩⟩
    have hker_dim : Module.finrank K (LinearMap.ker φ) = Module.finrank K V' :=
      LinearEquiv.finrank_eq (LinearEquiv.ofInjective
        (V.subtype.domRestrict (LinearMap.ker φ))
        (fun a b hab => Subtype.ext (Subtype.ext hab)))
    have hrn := LinearMap.finrank_range_add_finrank_ker φ
    rw [hrange_eq, hker_dim] at hrn
    have hV'_row : V' ≤ LinearMap.range (rowProj b u) :=
      le_trans (fun z hz => ((hV'_mem z).mp hz).1) hVrow
    have hV'_supp : ∀ h ∈ V', ∀ w ∉ S.erase w₀, proj b u w h = 0 := by
      intro h hh w hw
      rcases (hV'_mem h).mp hh with ⟨hhV, h0⟩
      by_cases hww₀ : w = w₀
      · subst hww₀; exact h0
      · exact hVsupp h hhV w (fun hwS => hw (Finset.mem_erase.mpr ⟨hww₀, hwS⟩))
    have hinit_agree : ∀ w ∈ S.erase w₀,
        Module.finrank K (initSub b u V w) = Module.finrank K (initSub b u V' w) := by
      intro w hw
      have hne : w ≠ w₀ := (Finset.mem_erase.mp hw).1
      have hlt : colLexEquiv n w < colLexEquiv n w₀ :=
        lt_of_le_of_ne (hw₀max w (Finset.mem_erase.mp hw).2)
          (fun heq => hne ((colLexEquiv n).injective heq))
      have hfilt_eq : filtLe b u V w = filtLe b u V' w := by
        ext h
        change (h ∈ V ∧ ∀ w', colLexEquiv n w < colLexEquiv n w' → proj b u w' h = 0) ↔
          (h ∈ V' ∧ ∀ w', colLexEquiv n w < colLexEquiv n w' → proj b u w' h = 0)
        rw [hV'_mem]
        exact ⟨fun ⟨hhV, hgt⟩ => ⟨⟨hhV, hgt w₀ hlt⟩, hgt⟩,
          fun ⟨⟨hhV, _⟩, hgt⟩ => ⟨hhV, hgt⟩⟩
      unfold initSub; rw [hfilt_eq]
    have hsplit_sum := (Finset.add_sum_erase S
      (fun w => Module.finrank K (initSub b u V w)) hw₀S).symm
    rw [hsplit_sum, Finset.sum_congr rfl hinit_agree,
      ih (S.erase w₀) (by rw [Finset.card_erase_of_mem hw₀S]; omega) V' hV'_row hV'_supp, hrn]

lemma sum_finrank_initSub {I : Type*} [Fintype I] (b : I → (Fin n →₀ ℕ))
    (u : Fin n →₀ ℕ) (V : Submodule K (I → MatPoly K n))
    (hVrow : V ≤ LinearMap.range (rowProj b u)) :
    ∑ w ∈ M_col u, Module.finrank K (initSub b u V w) = Module.finrank K V :=
  sum_finrank_initSub_aux b u (M_col u).card (M_col u) rfl V hVrow
    (fun h _ w hw => proj_eq_zero_of_notMem_M_col b hw h)

lemma sum_finrank_piece_top (K : Type*) [Field K] {I : Type*} [Fintype I]
    (b : I → (Fin n →₀ ℕ)) (u : Fin n →₀ ℕ) :
    ∑ w ∈ M_col u, Module.finrank K
        (piece b (⊤ : Submodule (MatPoly K n) (I → MatPoly K n)) u w) =
      Module.finrank K (rowPiece b (⊤ : Submodule (MatPoly K n) (I → MatPoly K n)) u) := by
  have htop_row : rowPiece b (⊤ : Submodule (MatPoly K n) (I → MatPoly K n)) u =
      LinearMap.range (rowProj b u) := by
    unfold rowPiece; rw [Submodule.restrictScalars_top, top_inf_eq]
  rw [htop_row, ← sum_finrank_initSub b u (LinearMap.range (rowProj b u)) le_rfl]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have hpiece_eq : initSub b u (LinearMap.range (rowProj b u)) w =
      piece b (⊤ : Submodule (MatPoly K n) (I → MatPoly K n)) u w := by
    unfold piece
    rw [Submodule.restrictScalars_top, top_inf_eq]
    apply le_antisymm
    · rintro _ ⟨_, _, rfl⟩; exact ⟨_, rfl⟩
    · rintro _ ⟨x, rfl⟩
      refine ⟨proj b u w x, ⟨⟨proj b u w x, by rw [rowProj_proj, if_pos rfl]⟩, ?_⟩,
        by rw [proj_proj, if_pos ⟨rfl, rfl⟩]⟩
      intro w' hw'
      have hne : w' ≠ w := fun heq => ne_of_lt hw' (congrArg (colLexEquiv n) heq.symm)
      rw [proj_proj, if_neg (fun hc => hne hc.2)]
  rw [hpiece_eq]

/-! ### Computing `prodMulFactor univ (HSeries K b ⊤ ⊥)` via `J_sub` -/

def J_sub {I : Type*} (S : Finset (Fin n × Fin n)) :
    Submodule (MatPoly K n) (I → MatPoly K n) where
  carrier := { y | ∀ p : I, ∀ m ∈ (y p).support, ¬ (∀ v ∈ m.support, v ∈ S) }
  zero_mem' p m hm := by simp at hm
  add_mem' {y₁ y₂} h₁ h₂ p m hm := by
    rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with hm₁ | hm₂
    · exact h₁ p m hm₁
    · exact h₂ p m hm₂
  smul_mem' f {y} hy p m hm hsub := by
    rcases Finset.mem_add.mp (MvPolynomial.support_mul f (y p) hm) with ⟨m₁, _, m₂, hm₂, rfl⟩
    refine hy p m₂ hm₂ (fun v hv => hsub v ?_)
    rw [Finsupp.mem_support_iff] at hv ⊢
    simp [hv]

lemma isBigraded_J_sub {I : Type*} (b : I → (Fin n →₀ ℕ)) (S : Finset (Fin n × Fin n)) :
    IsBigraded b (J_sub S : Submodule (MatPoly K n) (I → MatPoly K n)) := by
  intro y hy u w p m hm
  rw [MvPolynomial.mem_support_iff] at hm
  simp only [proj, LinearMap.coe_mk, AddHom.coe_mk, coeff_filterPoly] at hm
  split_ifs at hm with hcond
  · exact hy p m (MvPolynomial.mem_support_iff.mpr hm)
  · exact False.elim (hm rfl)

lemma J_sub_univ {I : Type*} :
    (J_sub Finset.univ : Submodule (MatPoly K n) (I → MatPoly K n)) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]
  ext p m
  rw [Pi.zero_apply, MvPolynomial.coeff_zero]
  by_contra hm
  exact hy p m (MvPolynomial.mem_support_iff.mpr hm) (fun v _ => Finset.mem_univ v)

lemma J_sub_coker {I : Type*} {v₀ : Fin n × Fin n} {S : Finset (Fin n × Fin n)}
    (hv₀S : v₀ ∉ S) :
    (J_sub (insert v₀ S) : Submodule (MatPoly K n) (I → MatPoly K n)) ⊔
      Submodule.map (mulXLin v₀) ⊤ = J_sub S := by
  apply le_antisymm
  · refine sup_le (fun y hy p m hm hsub =>
        hy p m hm (fun v hv => Finset.mem_insert_of_mem (hsub v hv))) ?_
    rintro _ ⟨y, _, rfl⟩ p m hm hsub
    have hcoeff : MvPolynomial.coeff m (MvPolynomial.X v₀ * y p) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hm
    rw [coeff_X_mul_poly] at hcoeff
    split_ifs at hcoeff with hle
    · have hv₀ : v₀ ∈ m.support := by
        rw [Finsupp.mem_support_iff]
        have := hle v₀; simp at this; omega
      exact hv₀S (hsub v₀ hv₀)
    · exact False.elim (hcoeff rfl)
  · intro y hy
    set y₁ : I → MatPoly K n :=
      fun p => filterPoly (fun m => ¬ (Finsupp.single v₀ 1 ≤ m)) (y p)
    set y₂_pre : I → MatPoly K n :=
      fun p => ∑ m ∈ (y p).support,
        if Finsupp.single v₀ 1 ≤ m then
          MvPolynomial.monomial (m - Finsupp.single v₀ 1) (MvPolynomial.coeff m (y p))
        else 0
    have hy_eq : y = y₁ + mulXLin v₀ y₂_pre := by
      ext p m
      simp only [Pi.add_apply, y₁, y₂_pre, mulXLin, LinearMap.coe_mk, AddHom.coe_mk,
        coeff_filterPoly, coeff_X_mul_poly, MvPolynomial.coeff_add]
      by_cases hle : Finsupp.single v₀ 1 ≤ m
      · rw [if_neg (not_not.mpr hle), if_pos hle, zero_add, MvPolynomial.coeff_sum]
        by_cases hm : m ∈ (y p).support
        · rw [Finset.sum_eq_single m]
          · rw [if_pos hle, MvPolynomial.coeff_monomial, if_pos rfl]
          · intro m' _ hne
            split_ifs with hle'
            · have hsub_ne : m' - Finsupp.single v₀ 1 ≠ m - Finsupp.single v₀ 1 := by
                intro hc; apply hne; ext z
                have hz1 := hle z; have hz2 := hle' z
                have hcz := congrArg (fun g : _ →₀ ℕ => g z) hc
                simp at hz1 hz2 hcz ⊢; omega
              rw [MvPolynomial.coeff_monomial, if_neg hsub_ne]
            · simp
          · intro hnot; exact False.elim (hnot hm)
        · rw [MvPolynomial.notMem_support_iff.mp hm, Finset.sum_eq_zero]
          intro m' hm'
          have hne : m' ≠ m := fun h => hm (h ▸ hm')
          split_ifs with hle'
          · have hsub_ne : m' - Finsupp.single v₀ 1 ≠ m - Finsupp.single v₀ 1 := by
              intro hc; apply hne; ext z
              have hz1 := hle z; have hz2 := hle' z
              have hcz := congrArg (fun g : _ →₀ ℕ => g z) hc
              simp at hz1 hz2 hcz ⊢; omega
            rw [MvPolynomial.coeff_monomial, if_neg hsub_ne]
          · simp
      · rw [if_pos hle, if_neg hle, add_zero]
    have hy₁_mem : y₁ ∈ J_sub (insert v₀ S) := by
      intro p m hm hsub
      rw [MvPolynomial.mem_support_iff] at hm
      dsimp only [y₁] at hm
      rw [coeff_filterPoly] at hm
      by_cases hle' : Finsupp.single v₀ 1 ≤ m
      · rw [if_neg (not_not.mpr hle')] at hm
        exact False.elim (hm rfl)
      · rw [if_pos hle'] at hm
        have hm_y : m ∈ (y p).support := MvPolynomial.mem_support_iff.mpr hm
        refine hy p m hm_y (fun v hv => ?_)
        rcases Finset.mem_insert.mp (hsub v hv) with rfl | hvS
        · exfalso
          refine hle' (fun z => ?_)
          simp only [Finsupp.single_apply]
          by_cases hzv : v = z
          · subst hzv
            have hv0 : m v ≠ 0 := Finsupp.mem_support_iff.mp hv
            rw [if_pos rfl]; omega
          · rw [if_neg hzv]; exact Nat.zero_le _
        · exact hvS
    rw [hy_eq]
    exact Submodule.add_mem_sup hy₁_mem ⟨y₂_pre, trivial, rfl⟩

lemma J_sub_ker {I : Type*} (v₀ : Fin n × Fin n) (S : Finset (Fin n × Fin n))
    (hv₀ : v₀ ∈ S) :
    (⊤ : Submodule (MatPoly K n) (I → MatPoly K n)) ⊓
      Submodule.comap (mulXLin v₀) (J_sub S) = J_sub S := by
  apply le_antisymm
  · intro y hy p m hm hsub
    have hmul_mem : m + Finsupp.single v₀ 1 ∈ (mulXLin v₀ y p).support := by
      rw [MvPolynomial.mem_support_iff]
      simp only [mulXLin, LinearMap.coe_mk, AddHom.coe_mk, coeff_X_mul_poly]
      have hle : Finsupp.single v₀ 1 ≤ m + Finsupp.single v₀ 1 := fun z => by simp
      have hsub_eq : m + Finsupp.single v₀ 1 - Finsupp.single v₀ 1 = m := by ext z; simp
      rw [if_pos hle, hsub_eq]
      exact MvPolynomial.mem_support_iff.mp hm
    refine hy.2 p (m + Finsupp.single v₀ 1) hmul_mem (fun v hv => ?_)
    by_cases hvv₀ : v = v₀
    · exact hvv₀ ▸ hv₀
    · apply hsub v
      rw [Finsupp.mem_support_iff] at hv ⊢
      have hv_eq : ((m + Finsupp.single v₀ 1 : (Fin n × Fin n) →₀ ℕ)) v = m v := by
        rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hvv₀), add_zero]
      rwa [hv_eq] at hv
  · intro y hy
    exact ⟨trivial, (J_sub S).smul_mem (MvPolynomial.X v₀) hy⟩

lemma HSeries_top_J_sub_empty (K : Type*) [Field K] {I : Type*} [Fintype I]
    (b : I → (Fin n →₀ ℕ)) :
    HSeries K b ⊤ (J_sub ∅) =
      polyToZaFun (∑ p : I, MvPolynomial.monomial (b p) (1 : APoly n)) := by
  funext u; ext w
  have hcoeff_H : MvPolynomial.coeff w (HSeries K b (⊤ : Submodule (MatPoly K n) (I → MatPoly K n))
      (J_sub ∅) u) =
        (Module.finrank K (piece b (⊤ : Submodule (MatPoly K n) (I → MatPoly K n)) u w) : ℤ) -
          (Module.finrank K (piece b (J_sub ∅ : Submodule (MatPoly K n) (I → MatPoly K n)) u w) : ℤ) := by
    unfold HSeries
    rw [MvPolynomial.coeff_sum]
    by_cases hw : w ∈ M_col u
    · rw [Finset.sum_eq_single w]
      · simp
      · intro w' _ hne; simp [MvPolynomial.coeff_monomial, hne]
      · intro hnot; exact False.elim (hnot hw)
    · rw [Finset.sum_eq_zero (fun w' hw' => by
        have hne : w' ≠ w := fun h => hw (h ▸ hw')
        simp [MvPolynomial.coeff_monomial, hne])]
      have hb₁ : piece b (⊤ : Submodule (MatPoly K n) (I → MatPoly K n)) u w = ⊥ := by
        rw [eq_bot_iff]; rintro _ ⟨_, y, rfl⟩
        rw [proj_eq_zero_of_notMem_M_col b hw y]; exact Submodule.zero_mem ⊥
      have hb₂ : piece b (J_sub ∅ : Submodule (MatPoly K n) (I → MatPoly K n)) u w = ⊥ := by
        rw [eq_bot_iff]; rintro _ ⟨_, y, rfl⟩
        rw [proj_eq_zero_of_notMem_M_col b hw y]; exact Submodule.zero_mem ⊥
      rw [hb₁, hb₂, finrank_bot, Nat.cast_zero, sub_self]
  rw [hcoeff_H]
  unfold polyToZaFun
  rw [MvPolynomial.coeff_sum]
  by_cases hw0 : w = 0
  · subst hw0
    have hm0_of_colDeg0 : ∀ m : (Fin n × Fin n) →₀ ℕ, colDeg m = 0 → m = 0 := by
      intro m hcol
      ext v
      by_contra hne
      have hpos : 0 < m v := Nat.pos_of_ne_zero hne
      have hsum : 0 < ∑ j : Fin n, colDeg m j := by
        rw [← sum_rowDeg_eq_sum_colDeg]
        have h1 : m v ≤ rowDeg m v.1 := apply_le_rowDeg m v
        have h2 : rowDeg m v.1 ≤ ∑ i : Fin n, rowDeg m i :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.1)
        omega
      rw [hcol] at hsum; simp at hsum
    have hJ_bot : piece b (J_sub ∅ : Submodule (MatPoly K n) (I → MatPoly K n)) u 0 = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨hzJ, x, rfl⟩
      rw [Submodule.mem_bot]
      ext p m
      simp only [proj, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, coeff_filterPoly,
        MvPolynomial.coeff_zero]
      split_ifs with hcond
      · have hm0 := hm0_of_colDeg0 m hcond.2
        subst hm0
        by_contra hne
        have hm_supp : (0 : (Fin n × Fin n) →₀ ℕ) ∈ (proj b u 0 x p).support := by
          rw [MvPolynomial.mem_support_iff]
          simp only [proj, LinearMap.coe_mk, AddHom.coe_mk, coeff_filterPoly,
            if_pos hcond]
          exact hne
        exact hzJ p 0 hm_supp (by simp)
      · rfl
    rw [hJ_bot, finrank_bot, Nat.cast_zero, sub_zero]
    let Φ : ({ p : I // b p = u } → K) ≃ₗ[K]
        piece b (⊤ : Submodule (MatPoly K n) (I → MatPoly K n)) u 0 :=
      { toFun := fun f =>
          ⟨fun p => if h : b p = u then MvPolynomial.C (f ⟨p, h⟩) else 0,
           ⟨trivial, (fun p => if h : b p = u then MvPolynomial.C (f ⟨p, h⟩) else 0), by
            ext p m
            simp only [proj, LinearMap.coe_mk, AddHom.coe_mk, coeff_filterPoly]
            by_cases hbp : b p = u
            · rw [dif_pos hbp]
              by_cases hm0 : m = 0
              · subst hm0; simp [rowDeg_zero, colDeg_zero, hbp]
              · rw [MvPolynomial.coeff_C, if_neg (Ne.symm hm0), ite_self]
            · rw [dif_neg hbp, MvPolynomial.coeff_zero, ite_self]⟩⟩
        invFun := fun z p => MvPolynomial.coeff 0 (z.1 p.1)
        map_add' := fun f g => by
          ext p m
          by_cases hbp : b p = u
          · simp [hbp, map_add]
          · simp [hbp]
        map_smul' := fun c f => by
          ext p m
          by_cases hbp : b p = u
          · simp [hbp, smul_eq_mul]
          · simp [hbp]
        left_inv := fun f => by
          ext ⟨p, hp⟩
          simp [hp]
        right_inv := fun ⟨z, _, x, hx⟩ => by
          ext p m
          dsimp only
          rw [← hx]
          simp only [proj, LinearMap.coe_mk, AddHom.coe_mk, coeff_filterPoly]
          by_cases hbp : b p = u
          · rw [dif_pos hbp]
            by_cases hm0 : m = 0
            · subst hm0
              simp [rowDeg_zero, colDeg_zero, hbp]
            · rw [MvPolynomial.coeff_C, if_neg (Ne.symm hm0)]
              split_ifs with hcond
              · exact False.elim (hm0 (hm0_of_colDeg0 m hcond.2))
              · rfl
          · rw [dif_neg hbp, MvPolynomial.coeff_zero]
            split_ifs with hcond
            · have hm0 := hm0_of_colDeg0 m hcond.2
              subst hm0; rw [rowDeg_zero, zero_add] at hcond
              exact False.elim (hbp hcond.1)
            · rfl }
    rw [← LinearEquiv.finrank_eq Φ, Module.finrank_pi, Fintype.card_subtype]
    simp only [MvPolynomial.coeff_monomial]
    have h1 : (1 : APoly n) = MvPolynomial.monomial 0 1 := rfl
    simp_rw [MvPolynomial.coeff_sum]
    calc (Finset.univ.filter (fun p : I => b p = u)).card
        = ∑ p : I, if b p = u then (1 : ℤ) else 0 := by
            rw [Finset.card_filter, Nat.cast_sum]
            refine Finset.sum_congr rfl (fun p _ => by split_ifs <;> simp)
      _ = ∑ x : I, MvPolynomial.coeff 0 (if b x = u then (1 : APoly n) else 0) := by
            refine Finset.sum_congr rfl (fun p _ => ?_)
            by_cases hp : b p = u
            · rw [if_pos hp, if_pos hp, h1, MvPolynomial.coeff_monomial, if_pos rfl]
            · rw [if_neg hp, if_neg hp, MvPolynomial.coeff_zero]
  · have hpiece_eq : piece b (J_sub ∅ : Submodule (MatPoly K n) (I → MatPoly K n)) u w =
        piece b ⊤ u w := by
      refine le_antisymm (inf_le_inf_right _ le_top) ?_
      rintro _ ⟨_, x, rfl⟩
      refine ⟨?_, x, rfl⟩
      intro p m hm hsub
      rw [MvPolynomial.mem_support_iff] at hm
      simp only [proj, LinearMap.coe_mk, AddHom.coe_mk, coeff_filterPoly] at hm
      split_ifs at hm with hcond
      · have hm0 : m = 0 := by
          ext v; by_contra hv; exact Finset.notMem_empty v (hsub v (Finsupp.mem_support_iff.mpr hv))
        subst hm0
        exact hw0 (hcond.2.symm.trans colDeg_zero)
      · exact False.elim (hm rfl)
    rw [hpiece_eq, sub_self]
    symm
    rw [MvPolynomial.coeff_sum]
    refine Finset.sum_eq_zero (fun p _ => ?_)
    rw [MvPolynomial.coeff_monomial]
    split_ifs with hbp
    · change MvPolynomial.coeff w (MvPolynomial.monomial 0 (1 : ℤ)) = 0
      rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hw0)]
    · simp

lemma prodMulFactor_HSeries_top_J_sub (K : Type*) [Field K] {I : Type*} [Fintype I]
    (b : I → (Fin n →₀ ℕ)) (S : Finset (Fin n × Fin n)) :
    prodMulFactor S (HSeries K b ⊤ (J_sub S)) =
      polyToZaFun (∑ p : I, MvPolynomial.monomial (b p) (1 : APoly n)) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [prodMulFactor_empty]
    exact HSeries_top_J_sub_empty K b
  | insert v₀ S hv₀ ih =>
    rw [prodMulFactor_insert_right hv₀,
      mulFactor_HSeries b v₀ le_top (isBigraded_top b) (isBigraded_J_sub b _),
      J_sub_coker hv₀, J_sub_ker v₀ (insert v₀ S) (Finset.mem_insert_self v₀ S),
      HSeries_self, zaShift_zero, sub_zero, ih]

lemma prodMulFactor_univ_HSeries_top_bot (K : Type*) [Field K] {I : Type*} [Fintype I]
    (b : I → (Fin n →₀ ℕ)) :
    prodMulFactor Finset.univ (HSeries K b ⊤ ⊥) =
      polyToZaFun (∑ p : I, MvPolynomial.monomial (b p) (1 : APoly n)) := by
  rw [← J_sub_univ]
  exact prodMulFactor_HSeries_top_J_sub K b Finset.univ

/-! ### Section 5: Noetherian `ker`/`coker` Induction and Initial Submodule `N^♯` -/

lemma nonconst_poly_smul_mem_of_all_X_kill {I : Type*}
    {U V : Submodule (MatPoly K n) (I → MatPoly K n)}
    (hkill : ∀ v : Fin n × Fin n, ∀ y ∈ U, (MvPolynomial.X v : MatPoly K n) • y ∈ V)
    (f : MatPoly K n) {y : I → MatPoly K n} (hy : y ∈ U) :
    (f - MvPolynomial.C (MvPolynomial.constantCoeff f)) • y ∈ V := by
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    by_cases hm0 : m = 0
    · subst hm0
      have hC : MvPolynomial.constantCoeff (MvPolynomial.monomial (0 : (Fin n × Fin n) →₀ ℕ) c) = c := by
        simp [MvPolynomial.constantCoeff_monomial]
      have hM : (MvPolynomial.monomial (0 : (Fin n × Fin n) →₀ ℕ) c : MatPoly K n) = MvPolynomial.C c := by
        ext m'; simp [MvPolynomial.coeff_C, eq_comm]
      rw [hC, hM, sub_self, zero_smul]
      exact V.zero_mem
    · have hC : MvPolynomial.constantCoeff (MvPolynomial.monomial m c) = 0 := by
        simp [MvPolynomial.constantCoeff_monomial, hm0]
      rw [hC, map_zero, sub_zero]
      have hsupp : m.support.Nonempty := Finsupp.support_nonempty_iff.mpr hm0
      obtain ⟨v, hv⟩ := hsupp
      have hv_pos : 1 ≤ m v := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)
      have hsplit_m : m = Finsupp.single v 1 + (m - Finsupp.single v 1) := by
        ext z
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        by_cases hzv : v = z
        · subst hzv; rw [if_pos rfl]; omega
        · rw [if_neg hzv]; omega
      have hX_split : MvPolynomial.monomial m c =
          MvPolynomial.X v * MvPolynomial.monomial (m - Finsupp.single v 1) c := by
        have hX : (MvPolynomial.X v : MatPoly K n) = MvPolynomial.monomial (Finsupp.single v 1) 1 := by
          ext m'; simp [MvPolynomial.coeff_X, eq_comm]
        rw [hX, MvPolynomial.monomial_mul, one_mul, ← hsplit_m]
      rw [hX_split, mul_smul]
      exact hkill v _ (U.smul_mem _ hy)
  | add f₁ f₂ ih₁ ih₂ =>
    have hsplit : f₁ + f₂ - MvPolynomial.C (MvPolynomial.constantCoeff (f₁ + f₂)) =
        (f₁ - MvPolynomial.C (MvPolynomial.constantCoeff f₁)) +
          (f₂ - MvPolynomial.C (MvPolynomial.constantCoeff f₂)) := by
      rw [map_add, map_add]; ring
    rw [hsplit, add_smul]
    exact V.add_mem ih₁ ih₂

lemma kPoly_exists_of_kill_outside {I : Type*} [Fintype I] (b : I → (Fin n →₀ ℕ))
    (S : Finset (Fin n × Fin n))
    {U V : Submodule (MatPoly K n) (I → MatPoly K n)}
    (hVU : V ≤ U) (hU : IsBigraded b U) (hV : IsBigraded b V)
    (hkill : ∀ v : Fin n × Fin n, v ∉ S → ∀ y ∈ U, (MvPolynomial.X v : MatPoly K n) • y ∈ V) :
    ∃ Q : ZaPoly n, polyToZaFun Q = prodMulFactor S (HSeries K b U V) := by
  induction S using Finset.induction_on generalizing U V with
  | empty =>
    rw [prodMulFactor_empty]
    have hNoethRing : IsNoetherianRing (MatPoly K n) := MvPolynomial.isNoetherianRing
    have hFinMod : Module.Finite (MatPoly K n) (I → MatPoly K n) := inferInstance
    have hNoethMod : IsNoetherian (MatPoly K n) (I → MatPoly K n) := inferInstance
    obtain ⟨G, hG⟩ := hNoethMod.noetherian U
    have hmodV : ∀ y ∈ U, ∃ c : (I → MatPoly K n) → K,
        y - ∑ g ∈ G, (MvPolynomial.C (c g) : MatPoly K n) • g ∈ V := by
      intro y hy
      rw [← hG] at hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · intro g hg
        refine ⟨fun g' => if g' = g then 1 else 0, ?_⟩
        have hsum : ∑ g' ∈ G,
            (MvPolynomial.C (if g' = g then (1 : K) else 0) : MatPoly K n) • g' = g := by
          rw [Finset.sum_eq_single g]
          · simp
          · intro g' _ hne; simp [hne]
          · intro hnot; exact False.elim (hnot (Finset.mem_coe.mp hg))
        rw [hsum, sub_self]; exact V.zero_mem
      · refine ⟨fun _ => 0, ?_⟩
        simp [V.zero_mem]
      · rintro y₁ y₂ _ _ ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩
        refine ⟨fun g => c₁ g + c₂ g, ?_⟩
        have hsum : (y₁ + y₂) - ∑ g ∈ G, (MvPolynomial.C (c₁ g + c₂ g) : MatPoly K n) • g =
            (y₁ - ∑ g ∈ G, (MvPolynomial.C (c₁ g) : MatPoly K n) • g) +
              (y₂ - ∑ g ∈ G, (MvPolynomial.C (c₂ g) : MatPoly K n) • g) := by
          simp only [map_add, add_smul, Finset.sum_add_distrib]
          abel
        rw [hsum]; exact V.add_mem hc₁ hc₂
      · rintro f y₀ hy₀ ⟨c₀, hc₀⟩
        have hy₀U : y₀ ∈ U := by rw [← hG]; exact hy₀
        refine ⟨fun g => MvPolynomial.constantCoeff f * c₀ g, ?_⟩
        set cf : MatPoly K n := MvPolynomial.C (MvPolynomial.constantCoeff f)
        have h1 : (f - cf) • y₀ ∈ V :=
          nonconst_poly_smul_mem_of_all_X_kill
            (fun v z hz => hkill v (Finset.notMem_empty v) z hz) f hy₀U
        have h2 : cf • (y₀ - ∑ g ∈ G, (MvPolynomial.C (c₀ g) : MatPoly K n) • g) ∈ V :=
          V.smul_mem cf hc₀
        have heq : f • y₀ - ∑ g ∈ G,
              (MvPolynomial.C (MvPolynomial.constantCoeff f * c₀ g) : MatPoly K n) • g =
            (f - cf) • y₀ + cf • (y₀ - ∑ g ∈ G, (MvPolynomial.C (c₀ g) : MatPoly K n) • g) := by
          funext p
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply,
            smul_eq_mul, map_mul, cf, mul_sub, sub_mul, Finset.mul_sum, mul_assoc]
          abel
        rw [heq]; exact V.add_mem h1 h2
    -- Finite set of row degrees supporting `G`:
    set suppU : Finset (Fin n →₀ ℕ) := G.biUnion (fun g =>
      Finset.univ.biUnion (fun p : I => (g p).support.image (fun m => rowDeg m + b p)))
    have hvanish : ∀ u ∉ suppU, HSeries K b U V u = 0 := by
      intro u hu
      have hprojG : ∀ g ∈ G, ∀ w, proj b u w g = 0 := by
        intro g hg w
        ext p m
        simp only [proj, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, coeff_filterPoly,
          MvPolynomial.coeff_zero]
        split_ifs with hcond
        · by_contra hne
          apply hu
          simp only [suppU, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
          exact ⟨g, hg, p, m, MvPolynomial.mem_support_iff.mpr hne, hcond.1⟩
        · rfl
      have hpiece_eq : ∀ w, piece b U u w = piece b V u w := by
        intro w
        refine le_antisymm ?_ (inf_le_inf_right _ hVU)
        rintro z ⟨hzU, x, rfl⟩
        obtain ⟨c, hc⟩ := hmodV (proj b u w x) hzU
        have hVproj : proj b u w
            (proj b u w x - ∑ g ∈ G, (MvPolynomial.C (c g) : MatPoly K n) • g) ∈ V :=
          hV _ hc u w
        rw [map_sub, proj_proj, if_pos ⟨rfl, rfl⟩] at hVproj
        have hG0 : proj b u w (∑ g ∈ G, (MvPolynomial.C (c g) : MatPoly K n) • g) = 0 := by
          have hCsmul : ∀ (k : K) (g : I → MatPoly K n),
              (MvPolynomial.C k : MatPoly K n) • g = k • g := by
            intro k g; ext p m; simp [MvPolynomial.coeff_C_mul, smul_eq_mul]
          simp_rw [hCsmul, map_sum, LinearMap.map_smul]
          exact Finset.sum_eq_zero (fun g hg => by rw [hprojG g hg w, smul_zero])
        rw [hG0, sub_zero] at hVproj
        exact ⟨hVproj, x, rfl⟩
      unfold HSeries
      refine Finset.sum_eq_zero (fun w _ => ?_)
      rw [hpiece_eq w, sub_self, map_zero]
    refine ⟨∑ u ∈ suppU, MvPolynomial.monomial u (HSeries K b U V u), ?_⟩
    funext u
    unfold polyToZaFun
    rw [MvPolynomial.coeff_sum]
    by_cases hu : u ∈ suppU
    · rw [Finset.sum_eq_single u]
      · simp
      · intro u' _ hne; simp [MvPolynomial.coeff_monomial, hne]
      · intro hnot; exact False.elim (hnot hu)
    · rw [Finset.sum_eq_zero (fun u' hu' => by
          have hne : u' ≠ u := fun h => hu (h ▸ hu')
          simp [MvPolynomial.coeff_monomial, hne]),
        hvanish u hu]
  | insert v₀ S hv₀S ih =>
    set Wc := V ⊔ Submodule.map (mulXLin v₀) U
    set Wk := U ⊓ Submodule.comap (mulXLin v₀) V
    have hWc_le : Wc ≤ U := sup_le hVU (by rintro _ ⟨y, hy, rfl⟩; exact U.smul_mem _ hy)
    have hWk_le : V ≤ Wk := fun y hy => ⟨hVU hy, V.smul_mem _ hy⟩
    have hWc_bg : IsBigraded b Wc := isBigraded_sup b hV (isBigraded_map_mulX b v₀ hU)
    have hWk_bg : IsBigraded b Wk := isBigraded_ker_mulX b v₀ hU hV
    have hkill_coker : ∀ v : Fin n × Fin n, v ∉ S → ∀ y ∈ U, (MvPolynomial.X v : MatPoly K n) • y ∈ Wc := by
      intro v hv y hy
      by_cases hvv₀ : v = v₀
      · subst hvv₀; exact Submodule.mem_sup_right ⟨y, hy, rfl⟩
      · exact Submodule.mem_sup_left (hkill v (fun h => hv (Finset.mem_of_mem_insert_of_ne h hvv₀)) y hy)
    have hkill_ker : ∀ v : Fin n × Fin n, v ∉ S → ∀ y ∈ Wk, (MvPolynomial.X v : MatPoly K n) • y ∈ V := by
      intro v hv y hy
      by_cases hvv₀ : v = v₀
      · subst hvv₀; exact hy.2
      · exact hkill v (fun h => hv (Finset.mem_of_mem_insert_of_ne h hvv₀)) y hy.1
    obtain ⟨Q₁, hQ₁⟩ := ih hWc_le hU hWc_bg hkill_coker
    obtain ⟨Q₂, hQ₂⟩ := ih hWk_le hWk_bg hV hkill_ker
    refine ⟨Q₁ - Z_var v₀.1 * A_var v₀.2 * Q₂, ?_⟩
    have hcomm : prodMulFactor (insert v₀ S) (HSeries K b U V) =
        prodMulFactor S (mulFactor v₀ (HSeries K b U V)) := by
      rw [prodMulFactor_insert hv₀S]
      unfold prodMulFactor
      induction S.toList with
      | nil => rfl
      | cons w ws ihL => simp only [List.foldr_cons, ← ihL, mulFactor_comm]
    rw [hcomm, mulFactor_HSeries b v₀ hVU hU hV, prodMulFactor_sub,
      prodMulFactor_zaShift_comm, ← hQ₁, ← hQ₂, ← polyToZaFun_Z_A_mul, ← polyToZaFun_sub]

def diagSet {n : ℕ} (τ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.image (fun i : Fin n => (i, τ i))

lemma kPoly_mem_JIdeal_of_diag_prod_kill {I : Type*} [Fintype I] (b : I → (Fin n →₀ ℕ))
    (τ : Equiv.Perm (Fin n)) :
    ∀ (L : List (Fin n)) {U V : Submodule (MatPoly K n) (I → MatPoly K n)},
      V ≤ U → IsBigraded b U → IsBigraded b V →
      (∀ v : Fin n × Fin n, v ∉ diagSet τ → ∀ y ∈ U, (MvPolynomial.X v : MatPoly K n) • y ∈ V) →
      (∀ y ∈ U, (L.map (fun i => (MvPolynomial.X (i, τ i) : MatPoly K n))).prod • y ∈ V) →
      ∃ Q : ZaPoly n, Q ∈ JIdeal τ ∧
        polyToZaFun Q = prodMulFactor (diagSet τ) (HSeries K b U V) := by
  intro L
  induction L with
  | nil =>
    intro U V hVU _ _ _ hprod
    have hUV : U = V := le_antisymm (fun y hy => by simpa using hprod y hy) hVU
    subst hUV
    refine ⟨0, (JIdeal τ).zero_mem, ?_⟩
    rw [HSeries_self, prodMulFactor_zero, polyToZaFun_zero]
  | cons i₀ L ih =>
    intro U V hVU hU hV hoff hprod
    set v₀ : Fin n × Fin n := (i₀, τ i₀)
    have hv₀_mem : v₀ ∈ diagSet τ :=
      Finset.mem_image.mpr ⟨i₀, Finset.mem_univ i₀, rfl⟩
    set W := V ⊔ Submodule.map (mulXLin v₀) U
    have hVW : V ≤ W := le_sup_left
    have hWU : W ≤ U := sup_le hVU (by rintro _ ⟨y, hy, rfl⟩; exact U.smul_mem _ hy)
    have hW_bg : IsBigraded b W := isBigraded_sup b hV (isBigraded_map_mulX b v₀ hU)
    -- Head `(U, W)` is killed outside `(diagSet τ).erase v₀`:
    have hkill_UW : ∀ v : Fin n × Fin n, v ∉ (diagSet τ).erase v₀ →
        ∀ y ∈ U, (MvPolynomial.X v : MatPoly K n) • y ∈ W := by
      intro v hv y hy
      by_cases hvv₀ : v = v₀
      · subst hvv₀; exact Submodule.mem_sup_right ⟨y, hy, rfl⟩
      · have hnotD : v ∉ diagSet τ := fun hD => hv (Finset.mem_erase.mpr ⟨hvv₀, hD⟩)
        exact Submodule.mem_sup_left (hoff v hnotD y hy)
    obtain ⟨Q₀, hQ₀⟩ := kPoly_exists_of_kill_outside b ((diagSet τ).erase v₀)
      hWU hU hW_bg hkill_UW
    set Q_head : ZaPoly n := (1 - Z_var i₀ * A_var (τ i₀)) * Q₀
    have hQ_head_mem : Q_head ∈ JIdeal τ :=
      Ideal.mul_mem_right Q₀ (JIdeal τ) (Ideal.subset_span ⟨i₀, rfl⟩)
    have hQ_head_eq : polyToZaFun Q_head = prodMulFactor (diagSet τ) (HSeries K b U W) := by
      change polyToZaFun ((1 - Z_var v₀.1 * A_var v₀.2) * Q₀) = _
      rw [polyToZaFun_one_sub_mul, hQ₀, prodMulFactor_erase hv₀_mem]
    -- Tail `(W, V)` is killed by `L.prod`:
    have hoff_W : ∀ v : Fin n × Fin n, v ∉ diagSet τ → ∀ y ∈ W,
        (MvPolynomial.X v : MatPoly K n) • y ∈ V :=
      fun v hv y hy => hoff v hv y (hWU hy)
    have hprod_W : ∀ y ∈ W,
        (L.map (fun i => (MvPolynomial.X (i, τ i) : MatPoly K n))).prod • y ∈ V := by
      intro y hy
      rcases Submodule.mem_sup.mp hy with ⟨y₁, hy₁, y₂, ⟨z, hzU, rfl⟩, rfl⟩
      rw [smul_add]
      refine V.add_mem (V.smul_mem _ hy₁) ?_
      change (L.map (fun i => (MvPolynomial.X (i, τ i) : MatPoly K n))).prod •
        ((MvPolynomial.X (i₀, τ i₀) : MatPoly K n) • z) ∈ V
      rw [smul_smul, mul_comm]
      exact hprod z hzU
    obtain ⟨Q_tail, hQ_tail_mem, hQ_tail_eq⟩ := ih hVW hW_bg hV hoff_W hprod_W
    refine ⟨Q_head + Q_tail, (JIdeal τ).add_mem hQ_head_mem hQ_tail_mem, ?_⟩
    rw [polyToZaFun_add, hQ_head_eq, hQ_tail_eq, ← prodMulFactor_add, ← HSeries_trans]

lemma kPoly_mem_JIdeal_of_D_annihilates {I : Type*} [Fintype I] (b : I → (Fin n →₀ ℕ))
    (c : Equiv.Perm (Fin n) → Kˣ) (τ : Equiv.Perm (Fin n))
    (T : Finset (Fin n × Fin n))
    {U V : Submodule (MatPoly K n) (I → MatPoly K n)}
    (hVU : V ≤ U) (hU : IsBigraded b U) (hV : IsBigraded b V)
    (hkill : ∀ v : Fin n × Fin n, v ∉ (T ∪ diagSet τ) →
      ∀ y ∈ U, (MvPolynomial.X v : MatPoly K n) • y ∈ V)
    (hD : ∀ y ∈ U, DetSupportRank.DeterminantSupport.determinantSupportPolynomial c • y ∈ V) :
    ∃ Q : ZaPoly n, Q ∈ JIdeal τ ∧
      polyToZaFun Q = prodMulFactor (T ∪ diagSet τ) (HSeries K b U V) := by
  induction T using Finset.induction_on generalizing U V with
  | empty =>
    rw [Finset.empty_union] at hkill ⊢
    -- Deduce `(∏ i, X (i, τ i)) • y ∈ V` from `D • y ∈ V` and off-diagonal vanishing:
    have hdiag_prod : ∀ y ∈ U,
        ((List.finRange n).map (fun i => (MvPolynomial.X (i, τ i) : MatPoly K n))).prod • y ∈ V := by
      intro y hy
      rw [← Fin.prod_univ_def]
      have hoff_term : ∀ σ : Equiv.Perm (Fin n), σ ≠ τ →
          (MvPolynomial.C (c σ : K) * ∏ i : Fin n, MvPolynomial.X (i, σ i)) • y ∈ V := by
        intro σ hστ
        have hex : ∃ i₀ : Fin n, σ i₀ ≠ τ i₀ := by
          by_contra hall
          push_neg at hall
          exact hστ (Equiv.ext hall)
        rcases hex with ⟨i₀, hi₀⟩
        have hnot_diag : (i₀, σ i₀) ∉ diagSet τ := by
          simp only [diagSet, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
          rintro i hi
          have h1 : i = i₀ := (Prod.mk.inj hi).1
          subst h1
          exact hi₀ (Prod.mk.inj hi).2.symm
        have hprod_eq : (∏ i : Fin n, (MvPolynomial.X (i, σ i) : MatPoly K n)) =
            MvPolynomial.X (i₀, σ i₀) *
              ∏ i ∈ (Finset.univ : Finset (Fin n)).erase i₀, MvPolynomial.X (i, σ i) :=
          (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)).symm
        rw [hprod_eq, ← mul_assoc, mul_comm (MvPolynomial.C _), mul_assoc, mul_smul]
        exact hkill (i₀, σ i₀) hnot_diag _ (U.smul_mem _ hy)
      have hD_y := hD y hy
      unfold DetSupportRank.DeterminantSupport.determinantSupportPolynomial at hD_y
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ τ), add_smul] at hD_y
      have hrest_mem : (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).erase τ,
          MvPolynomial.C (c σ : K) * ∏ i : Fin n, MvPolynomial.X (i, σ i)) • y ∈ V := by
        rw [Finset.sum_smul]
        exact V.sum_mem (fun σ hσ => hoff_term σ (Finset.ne_of_mem_erase hσ))
      have hτ_mem : (MvPolynomial.C (c τ : K) * ∏ i : Fin n, MvPolynomial.X (i, τ i)) • y ∈ V := by
        have := V.sub_mem hD_y hrest_mem
        simpa [add_sub_cancel_right] using this
      have hunit' := V.smul_mem (MvPolynomial.C (↑((c τ)⁻¹) : K)) hτ_mem
      rw [smul_smul, ← mul_assoc, ← MvPolynomial.C_mul, Units.inv_mul, MvPolynomial.C_1,
        one_mul] at hunit'
      exact hunit'
    exact kPoly_mem_JIdeal_of_diag_prod_kill b τ (List.finRange n) hVU hU hV hkill hdiag_prod
  | insert v₀ T hv₀T ih =>
    by_cases hv₀_mem : v₀ ∈ T ∪ diagSet τ
    · have hunion : insert v₀ T ∪ diagSet τ = T ∪ diagSet τ := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert]
        rcases Finset.mem_union.mp hv₀_mem with hT | hD
        · exact ⟨fun h => by rcases h with (rfl | h1) | h2; exact Or.inl hT; exact Or.inl h1; exact Or.inr h2,
            fun h => by rcases h with h1 | h2; exact Or.inl (Or.inr h1); exact Or.inr h2⟩
        · exact ⟨fun h => by rcases h with (rfl | h1) | h2; exact Or.inr hD; exact Or.inl h1; exact Or.inr h2,
            fun h => by rcases h with h1 | h2; exact Or.inl (Or.inr h1); exact Or.inr h2⟩
      rw [hunion] at hkill ⊢
      exact ih hVU hU hV hkill hD
    · have hunion : insert v₀ T ∪ diagSet τ = insert v₀ (T ∪ diagSet τ) :=
        Finset.insert_union v₀ T (diagSet τ)
      rw [hunion] at hkill ⊢
      set Wc := V ⊔ Submodule.map (mulXLin v₀) U
      set Wk := U ⊓ Submodule.comap (mulXLin v₀) V
      have hWc_le : Wc ≤ U := sup_le hVU (by rintro _ ⟨y, hy, rfl⟩; exact U.smul_mem _ hy)
      have hWk_le : V ≤ Wk := fun y hy => ⟨hVU hy, V.smul_mem _ hy⟩
      have hWc_bg : IsBigraded b Wc := isBigraded_sup b hV (isBigraded_map_mulX b v₀ hU)
      have hWk_bg : IsBigraded b Wk := isBigraded_ker_mulX b v₀ hU hV
      have hkill_coker : ∀ v : Fin n × Fin n, v ∉ (T ∪ diagSet τ) →
          ∀ y ∈ U, (MvPolynomial.X v : MatPoly K n) • y ∈ Wc := by
        intro v hv y hy
        by_cases hvv₀ : v = v₀
        · subst hvv₀; exact Submodule.mem_sup_right ⟨y, hy, rfl⟩
        · exact Submodule.mem_sup_left
            (hkill v (fun h => hv (Finset.mem_of_mem_insert_of_ne h hvv₀)) y hy)
      have hkill_ker : ∀ v : Fin n × Fin n, v ∉ (T ∪ diagSet τ) →
          ∀ y ∈ Wk, (MvPolynomial.X v : MatPoly K n) • y ∈ V := by
        intro v hv y hy
        by_cases hvv₀ : v = v₀
        · subst hvv₀; exact hy.2
        · exact hkill v (fun h => hv (Finset.mem_of_mem_insert_of_ne h hvv₀)) y hy.1
      have hD_coker : ∀ y ∈ U,
          DetSupportRank.DeterminantSupport.determinantSupportPolynomial c • y ∈ Wc :=
        fun y hy => Submodule.mem_sup_left (hD y hy)
      have hD_ker : ∀ y ∈ Wk,
          DetSupportRank.DeterminantSupport.determinantSupportPolynomial c • y ∈ V :=
        fun y hy => hD y hy.1
      obtain ⟨Q₁, hQ₁_mem, hQ₁_eq⟩ := ih hWc_le hU hWc_bg hkill_coker hD_coker
      obtain ⟨Q₂, hQ₂_mem, hQ₂_eq⟩ := ih hWk_le hWk_bg hV hkill_ker hD_ker
      refine ⟨Q₁ - Z_var v₀.1 * A_var v₀.2 * Q₂,
        (JIdeal τ).sub_mem hQ₁_mem (Ideal.mul_mem_left _ _ hQ₂_mem), ?_⟩
      have hcomm : prodMulFactor (insert v₀ (T ∪ diagSet τ)) (HSeries K b U V) =
          prodMulFactor (T ∪ diagSet τ) (mulFactor v₀ (HSeries K b U V)) := by
        rw [prodMulFactor_insert hv₀_mem]
        unfold prodMulFactor
        induction (T ∪ diagSet τ).toList with
        | nil => rfl
        | cons w ws ihL => simp only [List.foldr_cons, ← ihL, mulFactor_comm]
      rw [hcomm, mulFactor_HSeries b v₀ hVU hU hV, prodMulFactor_sub,
        prodMulFactor_zaShift_comm, ← hQ₁_eq, ← hQ₂_eq, ← polyToZaFun_Z_A_mul, ← polyToZaFun_sub]

/-! ### Initial Submodule `N^♯` of `Im(A)` and Existence of `Q ∈ ⋂_τ J_τ` -/

lemma eval_D_at_perm (c : Equiv.Perm (Fin n) → Kˣ) (τ : Equiv.Perm (Fin n)) :
    MvPolynomial.eval (fun v : Fin n × Fin n => if v.2 = τ v.1 then (1 : K) else 0)
      (DetSupportRank.DeterminantSupport.determinantSupportPolynomial c) = (c τ : K) := by
  unfold DetSupportRank.DeterminantSupport.determinantSupportPolynomial
  rw [map_sum]
  rw [Finset.sum_eq_single τ]
  · simp
  · intro σ _ hne
    rw [map_mul, MvPolynomial.eval_C, map_prod]
    have hex : ∃ i₀ : Fin n, σ i₀ ≠ τ i₀ := by
      by_contra hall; push_neg at hall; exact hne (Equiv.ext hall)
    rcases hex with ⟨i₀, hi₀⟩
    have hp0 : (∏ i : Fin n,
        MvPolynomial.eval (fun v : Fin n × Fin n => if v.2 = τ v.1 then (1 : K) else 0)
          (MvPolynomial.X (i, σ i))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])
    rw [hp0, mul_zero]
  · intro hnot; exact False.elim (hnot (Finset.mem_univ τ))

lemma D_ne_zero (c : Equiv.Perm (Fin n) → Kˣ) :
    DetSupportRank.DeterminantSupport.determinantSupportPolynomial c ≠ 0 := by
  intro h0
  have h1 := eval_D_at_perm c 1
  rw [h0, map_zero] at h1
  exact Units.ne_zero (c 1) h1.symm

lemma D_rowDeg_colDeg (c : Equiv.Perm (Fin n) → Kˣ)
    {m : (Fin n × Fin n) →₀ ℕ}
    (hm : m ∈ (DetSupportRank.DeterminantSupport.determinantSupportPolynomial c).support) :
    rowDeg m = oneDeg n ∧ colDeg m = oneDeg n := by
  unfold DetSupportRank.DeterminantSupport.determinantSupportPolynomial at hm
  rcases Finset.mem_biUnion.mp (MvPolynomial.support_sum hm) with ⟨σ, _, hmσ⟩
  have hterm : MvPolynomial.C (c σ : K) * (∏ i : Fin n, MvPolynomial.X (i, σ i)) =
      MvPolynomial.monomial (∑ i : Fin n, Finsupp.single (i, σ i) 1) (c σ : K) := by
    have hprod : ∀ S : Finset (Fin n),
        (∏ i ∈ S, (MvPolynomial.X (i, σ i) : MatPoly K n)) =
          MvPolynomial.monomial (∑ i ∈ S, Finsupp.single (i, σ i) 1) 1 := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | insert i₀ S hi₀ ih =>
        have hX : (MvPolynomial.X (i₀, σ i₀) : MatPoly K n) =
            MvPolynomial.monomial (Finsupp.single (i₀, σ i₀) 1) 1 := by
          ext m'; simp [MvPolynomial.coeff_X, eq_comm]
        rw [Finset.prod_insert hi₀, Finset.sum_insert hi₀, ih, hX,
          MvPolynomial.monomial_mul, one_mul]
    have hC : (MvPolynomial.C (c σ : K) : MatPoly K n) = MvPolynomial.monomial 0 (c σ : K) := by
      ext m'; simp [MvPolynomial.coeff_C, eq_comm]
    rw [hprod Finset.univ, hC, MvPolynomial.monomial_mul, zero_add, mul_one]
  rw [hterm] at hmσ
  have hm_eq : m = ∑ i : Fin n, Finsupp.single (i, σ i) 1 :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hmσ)
  subst hm_eq
  have hmap_sum : ∀ (S : Finset (Fin n)),
      rowDeg (∑ i ∈ S, Finsupp.single (i, σ i) 1) = ∑ i ∈ S, Finsupp.single i 1 ∧
        colDeg (∑ i ∈ S, Finsupp.single (i, σ i) 1) = ∑ i ∈ S, Finsupp.single (σ i) 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [rowDeg_zero, colDeg_zero]
    | insert i₀ S hi₀ ih =>
      rw [Finset.sum_insert hi₀, Finset.sum_insert hi₀, Finset.sum_insert hi₀,
        rowDeg_add, colDeg_add, rowDeg_single, colDeg_single, ih.1, ih.2]
      exact ⟨rfl, rfl⟩
  rcases hmap_sum Finset.univ with ⟨hr, hc⟩
  refine ⟨hr, hc.trans ?_⟩
  exact Equiv.sum_comp σ (fun j => Finsupp.single j 1)

lemma exists_JIdeal_poly_of_koszul_pair {I : Type*} [Fintype I] [DecidableEq I]
    (c : Equiv.Perm (Fin n) → Kˣ)
    (A B : Matrix I I (MatPoly K n))
    (a b : I → (Fin n →₀ ℕ))
    (hAB : A * B = DetSupportRank.DeterminantSupport.determinantSupportPolynomial c • 1)
    (hBA : B * A = DetSupportRank.DeterminantSupport.determinantSupportPolynomial c • 1)
    (hA_deg : ∀ p q : I, ∀ m ∈ (A p q).support, rowDeg m + b p = a q) :
    ∃ Q : ZaPoly n, (∀ τ : Equiv.Perm (Fin n), Q ∈ JIdeal τ) ∧
      evalAOne n Q =
        (∑ p : I, MvPolynomial.monomial (b p) 1) -
          (∑ q : I, MvPolynomial.monomial (a q) 1) := by
  set D := DetSupportRank.DeterminantSupport.determinantSupportPolynomial c
  set φA : (I → MatPoly K n) →ₗ[MatPoly K n] (I → MatPoly K n) := Matrix.mulVecLin A
  set φB : (I → MatPoly K n) →ₗ[MatPoly K n] (I → MatPoly K n) := Matrix.mulVecLin B
  have hφBA : ∀ x : I → MatPoly K n, φB (φA x) = D • x := by
    intro x
    change Matrix.mulVec B (Matrix.mulVec A x) = D • x
    rw [Matrix.mulVec_mulVec, hBA]
    funext p
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hφAB : ∀ y : I → MatPoly K n, φA (φB y) = D • y := by
    intro y
    change Matrix.mulVec A (Matrix.mulVec B y) = D • y
    rw [Matrix.mulVec_mulVec, hAB]
    funext p
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hφA_inj : Function.Injective φA := by
    intro x₁ x₂ hx
    have hD_eq : D • x₁ = D • x₂ := by rw [← hφBA x₁, ← hφBA x₂, hx]
    funext q
    have hq : D * x₁ q = D * x₂ q := congrFun hD_eq q
    exact mul_left_cancel₀ (D_ne_zero c) hq
  -- Row-homogeneity of `φA`: `rowProj b u (φA x) = φA (rowProj a u x)`!
  have hrow_φA : ∀ (u : Fin n →₀ ℕ) (x : I → MatPoly K n),
      rowProj b u (φA x) = φA (rowProj a u x) := by
    intro u x
    ext p m
    simp only [rowProj, φA, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      LinearMap.coe_mk, AddHom.coe_mk, coeff_filterPoly, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_mul]
    by_cases hcond : rowDeg m + b p = u
    · rw [if_pos hcond]
      refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun mm hmm => ?_))
      by_cases hm1 : MvPolynomial.coeff mm.1 (A p q) = 0
      · rw [hm1, zero_mul, zero_mul]
      · have hdeg1 := hA_deg p q mm.1 (MvPolynomial.mem_support_iff.mpr hm1)
        have hsum_m : mm.1 + mm.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hmm
        have hm2_cond : rowDeg mm.2 + a q = u := by
          rw [← hcond, ← hsum_m, rowDeg_add, ← hdeg1]
          abel
        rw [if_pos hm2_cond]
    · rw [if_neg hcond]
      symm
      refine Finset.sum_eq_zero (fun q _ => Finset.sum_eq_zero (fun mm hmm => ?_))
      by_cases hm1 : MvPolynomial.coeff mm.1 (A p q) = 0
      · rw [hm1, zero_mul]
      · have hdeg1 := hA_deg p q mm.1 (MvPolynomial.mem_support_iff.mpr hm1)
        have hsum_m : mm.1 + mm.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hmm
        have hm2_not : ¬ (rowDeg mm.2 + a q = u) := by
          intro hc; apply hcond
          rw [← hsum_m, rowDeg_add, ← hc, ← hdeg1]
          abel
        rw [if_neg hm2_not, mul_zero]
  set N : Submodule (MatPoly K n) (I → MatPoly K n) := LinearMap.range φA
  have hfinrank_N : ∀ u : Fin n →₀ ℕ,
      Module.finrank K (rowPiece b N u) =
        Module.finrank K (rowPiece a (⊤ : Submodule (MatPoly K n) (I → MatPoly K n)) u) := by
    intro u
    let ψ : rowPiece a (⊤ : Submodule (MatPoly K n) (I → MatPoly K n)) u ≃ₗ[K] rowPiece b N u :=
      { toFun := fun x =>
          ⟨φA x.1, ⟨⟨x.1, rfl⟩, φA x.1, by
            rcases x.2.2 with ⟨z, hz⟩
            have hrx : rowProj a u x.1 = x.1 := by
              rw [← hz]; ext p m; simp only [rowProj, LinearMap.coe_mk, AddHom.coe_mk,
                coeff_filterPoly]; split_ifs <;> rfl
            rw [hrow_φA, hrx]⟩⟩
        invFun := fun y =>
          ⟨rowProj a u (Classical.choose y.2.1), ⟨trivial, _, rfl⟩⟩
        map_add' := fun x₁ x₂ => Subtype.ext (map_add φA x₁.1 x₂.1)
        map_smul' := fun k x => Subtype.ext (by
          rw [RingHom.id_apply]
          change φA (k • x.1) = k • φA x.1
          have hCk : ∀ z : I → MatPoly K n, k • z = (MvPolynomial.C k : MatPoly K n) • z := by
            intro z; ext p m; simp [MvPolynomial.coeff_C_mul, smul_eq_mul]
          rw [hCk x.1, hCk (φA x.1), LinearMap.map_smul])
        left_inv := fun x => by
          apply Subtype.ext; dsimp only
          have hchoose : φA (Classical.choose (⟨x.1, rfl⟩ : φA x.1 ∈ N)) = φA x.1 :=
            Classical.choose_spec (⟨x.1, rfl⟩ : φA x.1 ∈ N)
          have heq := hφA_inj hchoose
          rcases x.2.2 with ⟨z, hz⟩
          rw [heq, ← hz]
          ext p m; simp only [rowProj, LinearMap.coe_mk, AddHom.coe_mk, coeff_filterPoly]
          split_ifs <;> rfl
        right_inv := fun y => by
          apply Subtype.ext; dsimp only
          have hchoose : φA (Classical.choose y.2.1) = y.1 := Classical.choose_spec y.2.1
          rw [← hrow_φA, hchoose]
          rcases y.2.2 with ⟨z, hz⟩
          rw [← hz]
          ext p m; simp only [rowProj, LinearMap.coe_mk, AddHom.coe_mk, coeff_filterPoly]
          split_ifs <;> rfl }
    exact (LinearEquiv.finrank_eq ψ).symm
  -- Construct initial submodule `N_sharp : Submodule (MatPoly K n) (I → MatPoly K n)`:
  have hsmul_init : ∀ (v : Fin n × Fin n) (u w : Fin n →₀ ℕ) (z : I → MatPoly K n),
      z ∈ initSub b u (rowPiece b N u) w →
        mulXLin v z ∈ initSub b (u + Finsupp.single v.1 1)
          (rowPiece b N (u + Finsupp.single v.1 1)) (w + Finsupp.single v.2 1) := by
    intro v u w z ⟨h, ⟨⟨hhN, hhRow⟩, hhGt⟩, hzh⟩
    set u' := u + Finsupp.single v.1 1
    set w' := w + Finsupp.single v.2 1
    set h' := mulXLin v h
    have hh'N : h' ∈ N := N.smul_mem (MvPolynomial.X v) hhN
    have hh'Row : h' ∈ LinearMap.range (rowProj b u') := by
      rcases hhRow with ⟨x₀, rfl⟩
      refine ⟨h', ?_⟩
      rw [rowProj_eq_sum_proj b u x₀, map_sum] at *
      have hsum_eq : h' = ∑ w₀ ∈ M_col u, mulXLin v (proj b u w₀ x₀) := by
        dsimp [h']; rw [rowProj_eq_sum_proj, map_sum]
      rw [hsum_eq, map_sum]
      refine Finset.sum_congr rfl (fun w₀ _ => ?_)
      have hproj_v : mulXLin v (proj b u w₀ x₀) =
          proj b u' (w₀ + Finsupp.single v.2 1) (mulXLin v x₀) := by
        rw [proj_mulX]
        have hle : Finsupp.single v.1 1 ≤ u' ∧ Finsupp.single v.2 1 ≤ w₀ + Finsupp.single v.2 1 :=
          ⟨fun i => by simp [u'], fun j => by simp⟩
        rw [if_pos hle]
        have hu_sub : u' - Finsupp.single v.1 1 = u := by ext i; simp [u']
        have hw_sub : w₀ + Finsupp.single v.2 1 - Finsupp.single v.2 1 = w₀ := by ext j; simp
        rw [hu_sub, hw_sub]
      rw [hproj_v, rowProj_proj, if_pos rfl]
    have hh'Gt : ∀ w'' : Fin n →₀ ℕ, colLexEquiv n w' < colLexEquiv n w'' →
        proj b u' w'' h' = 0 := by
      intro w'' hw''
      rw [proj_mulX]
      split_ifs with hle
      · have hsplit_w'' : w'' = (w'' - Finsupp.single v.2 1) + Finsupp.single v.2 1 := by
          ext j; have := hle.2 j; simp at this ⊢; omega
        rw [hsplit_w''] at hw''
        have hlt_sub : colLexEquiv n w < colLexEquiv n (w'' - Finsupp.single v.2 1) :=
          (colLex_add_lt_iff w (w'' - Finsupp.single v.2 1) (Finsupp.single v.2 1)).mp hw''
        have hu_sub : u' - Finsupp.single v.1 1 = u := by ext i; simp [u']
        rw [hu_sub, hhGt _ hlt_sub, map_zero]
      · rfl
    refine ⟨h', ⟨⟨hh'N, hh'Row⟩, hh'Gt⟩, ?_⟩
    rw [proj_mulX]
    have hle : Finsupp.single v.1 1 ≤ u' ∧ Finsupp.single v.2 1 ≤ w' :=
      ⟨fun i => by simp [u'], fun j => by simp [w']⟩
    rw [if_pos hle]
    have hu_sub : u' - Finsupp.single v.1 1 = u := by ext i; simp [u']
    have hw_sub : w' - Finsupp.single v.2 1 = w := by ext j; simp [w']
    rw [hu_sub, hw_sub, hzh]
  let N_sharp : Submodule (MatPoly K n) (I → MatPoly K n) :=
    { carrier := { x | ∀ u w, proj b u w x ∈ initSub b u (rowPiece b N u) w }
      zero_mem' := fun u w => by rw [map_zero]; exact (initSub b u (rowPiece b N u) w).zero_mem
      add_mem' := fun hx hy u w => by
        rw [map_add]; exact (initSub b u (rowPiece b N u) w).add_mem (hx u w) (hy u w)
      smul_mem' := fun f {x} hx => by
        induction f using MvPolynomial.induction_on with
        | C k =>
          intro u w
          have hCk : (MvPolynomial.C k : MatPoly K n) • x = k • x := by
            ext p m; simp [MvPolynomial.coeff_C_mul, smul_eq_mul]
          rw [hCk, LinearMap.map_smul]
          exact (initSub b u (rowPiece b N u) w).smul_mem k (hx u w)
        | add f₁ f₂ ih₁ ih₂ =>
          intro u w; rw [add_smul, map_add]
          exact (initSub b u (rowPiece b N u) w).add_mem (ih₁ u w) (ih₂ u w)
        | mul_X f₀ v ih =>
          intro u w
          rw [mul_comm f₀, mul_smul]
          change proj b u w (mulXLin v (f₀ • x)) ∈ _
          rw [proj_mulX]
          split_ifs with hle
          · have hz := hsmul_init v (u - Finsupp.single v.1 1) (w - Finsupp.single v.2 1)
              (proj b (u - Finsupp.single v.1 1) (w - Finsupp.single v.2 1) (f₀ • x)) (ih _ _)
            have hu_add : u - Finsupp.single v.1 1 + Finsupp.single v.1 1 = u := by
              ext i; have := hle.1 i; simp at this ⊢; omega
            have hw_add : w - Finsupp.single v.2 1 + Finsupp.single v.2 1 = w := by
              ext j; have := hle.2 j; simp at this ⊢; omega
            rwa [hu_add, hw_add] at hz
          · exact (initSub b u (rowPiece b N u) w).zero_mem }
  have hN_sharp_bg : IsBigraded b N_sharp := by
    intro x hx u w u' w'
    rw [proj_proj]
    split_ifs with heq
    · rcases heq with ⟨rfl, rfl⟩; exact hx _ _
    · exact (initSub b u' (rowPiece b N u') w').zero_mem
  have hpiece_N_sharp : ∀ u w, piece b N_sharp u w = initSub b u (rowPiece b N u) w := by
    intro u w
    apply le_antisymm
    · rintro _ ⟨hx, y, rfl⟩
      have h := hx u w
      rwa [proj_proj, if_pos ⟨rfl, rfl⟩] at h
    · intro z hz
      rcases hz with ⟨h, hh, rfl⟩
      refine ⟨fun u' w' => ?_, h, rfl⟩
      rw [proj_proj]
      split_ifs with heq
      · rcases heq with ⟨rfl, rfl⟩; exact ⟨h, hh, rfl⟩
      · exact (initSub b u' (rowPiece b N u') w').zero_mem
  have hD_N_sharp : ∀ y : I → MatPoly K n, D • y ∈ N_sharp := by
    -- Suffices to show `D • Pi.single p 1 ∈ N_sharp` for every `p : I`:
    have hbasis : ∀ p : I, D • (Pi.single p (1 : MatPoly K n) : I → MatPoly K n) ∈ N_sharp := by
      intro p
      set ep : I → MatPoly K n := Pi.single p 1
      have hDep_N : D • ep ∈ N := ⟨φB ep, hφAB ep⟩
      have hDep_proj : proj b (oneDeg n + b p) (oneDeg n) (D • ep) = D • ep := by
        ext p' m
        simp only [proj, LinearMap.coe_mk, AddHom.coe_mk, coeff_filterPoly,
          Pi.smul_apply, smul_eq_mul, ep, Pi.single_apply]
        by_cases hp' : p' = p
        · subst hp'
          rw [if_pos rfl, mul_one]
          by_cases hm : m ∈ D.support
          · rcases D_rowDeg_colDeg c hm with ⟨hr, hc⟩
            rw [if_pos ⟨by rw [hr], hc⟩]
          · rw [MvPolynomial.notMem_support_iff.mp hm, ite_self]
        · rw [if_neg hp', mul_zero, MvPolynomial.coeff_zero, ite_self]
      have hDep_other : ∀ u' w', (u' ≠ oneDeg n + b p ∨ w' ≠ oneDeg n) →
          proj b u' w' (D • ep) = 0 := by
        intro u' w' hne
        rw [← hDep_proj, proj_proj, if_neg (fun hc => by rcases hne with h1 | h2; exact h1 hc.1; exact h2 hc.2)]
      have hDep_mem_init : D • ep ∈ initSub b (oneDeg n + b p)
          (rowPiece b N (oneDeg n + b p)) (oneDeg n) := by
        refine ⟨D • ep, ⟨⟨hDep_N, ?_⟩, ?_⟩, hDep_proj⟩
        · exact range_proj_le_range_rowProj b (oneDeg n + b p) (oneDeg n) ⟨D • ep, hDep_proj⟩
        · intro w' hw'
          exact hDep_other _ w' (Or.inr (fun heq => ne_of_lt hw' (congrArg (colLexEquiv n) heq.symm)))
      intro u w
      by_cases heq : u = oneDeg n + b p ∧ w = oneDeg n
      · rcases heq with ⟨rfl, rfl⟩
        rw [hDep_proj]; exact hDep_mem_init
      · rw [hDep_other u w (by tauto)]
        exact (initSub b u (rowPiece b N u) w).zero_mem
    intro y
    have hy_sum : y = ∑ p : I, (y p) • (Pi.single p (1 : MatPoly K n) : I → MatPoly K n) := by
      ext p₀; simp [Pi.single_apply]
    rw [hy_sum, Finset.smul_sum]
    refine N_sharp.sum_mem (fun p _ => ?_)
    rw [smul_comm]
    exact N_sharp.smul_mem (y p) (hbasis p)
  -- Apply `kPoly_mem_JIdeal_of_D_annihilates` with `T = Finset.univ` (`univ ∪ diagSet τ = univ`)!
  have huniv_diag : ∀ τ : Equiv.Perm (Fin n), Finset.univ ∪ diagSet τ = Finset.univ := by
    intro τ; ext v; simp
  have hexQ : ∀ τ : Equiv.Perm (Fin n), ∃ Q_τ : ZaPoly n, Q_τ ∈ JIdeal τ ∧
      polyToZaFun Q_τ = prodMulFactor Finset.univ (HSeries K b ⊤ N_sharp) := by
    intro τ
    obtain ⟨Q_τ, hmem, heq⟩ := kPoly_mem_JIdeal_of_D_annihilates b c τ Finset.univ
      le_top (isBigraded_top b) hN_sharp_bg
      (fun v hv => False.elim (hv (by rw [huniv_diag]; exact Finset.mem_univ v)))
      (fun y _ => hD_N_sharp y)
    rw [huniv_diag] at heq
    exact ⟨Q_τ, hmem, heq⟩
  obtain ⟨Q, hQ1_mem, hQ_eq⟩ := hexQ 1
  have hQ_all : ∀ τ : Equiv.Perm (Fin n), Q ∈ JIdeal τ := by
    intro τ
    obtain ⟨Q_τ, hmem, heq⟩ := hexQ τ
    have hQQ : Q = Q_τ := polyToZaFun_inj (hQ_eq.trans heq.symm)
    rwa [hQQ]
  -- Compute `evalAOne n Q`:
  have heval_H : evalAOneFun (HSeries K b ⊤ N_sharp) =
      evalAOneFun (HSeries K b ⊤ ⊥) - evalAOneFun (HSeries K a ⊤ ⊥) := by
    funext u
    have heval_mon : ∀ (s : I → (Fin n →₀ ℕ))
        (M₁ M₂ : Submodule (MatPoly K n) (I → MatPoly K n)),
        evalAOneFun (HSeries K s M₁ M₂) u =
          (∑ w ∈ M_col u, (Module.finrank K (piece s M₁ u w) : ℤ)) -
            (∑ w ∈ M_col u, (Module.finrank K (piece s M₂ u w) : ℤ)) := by
      intro s M₁ M₂
      unfold evalAOneFun HSeries
      rw [map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [MvPolynomial.eval_monomial]
      have h1 : (w.prod fun _ e => (1 : ℤ) ^ e) = 1 := by simp [Finsupp.prod]
      rw [h1, mul_one]
    simp only [Pi.sub_apply, heval_mon]
    have hbot : ∀ (s : I → (Fin n →₀ ℕ)),
        ∑ w ∈ M_col u, (Module.finrank K
          (piece s (⊥ : Submodule (MatPoly K n) (I → MatPoly K n)) u w) : ℤ) = 0 := by
      intro s
      refine Finset.sum_eq_zero (fun w _ => ?_)
      have hpb : piece s (⊥ : Submodule (MatPoly K n) (I → MatPoly K n)) u w = ⊥ := by
        unfold piece; rw [Submodule.restrictScalars_bot, bot_inf_eq]
      rw [hpb, finrank_bot, Nat.cast_zero]
    rw [hbot b, hbot a, sub_zero, sub_zero]
    have hNs : ∑ w ∈ M_col u, (Module.finrank K (piece b N_sharp u w) : ℤ) =
        (Module.finrank K (rowPiece a (⊤ : Submodule (MatPoly K n) (I → MatPoly K n)) u) : ℤ) := by
      have hcongr : ∑ w ∈ M_col u, (Module.finrank K (piece b N_sharp u w) : ℤ) =
          ∑ w ∈ M_col u, (Module.finrank K (initSub b u (rowPiece b N u) w) : ℤ) := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        have hpeq := hpiece_N_sharp u w
        have hfeq : Module.finrank K (piece b N_sharp u w) =
            Module.finrank K (initSub b u (rowPiece b N u) w) := by
          have : ∀ {A B : Submodule K (I → MatPoly K n)}, A = B →
              Module.finrank K A = Module.finrank K B := by rintro A B rfl; rfl
          exact this hpeq
        exact congrArg Nat.cast hfeq
      rw [hcongr, ← Nat.cast_sum, sum_finrank_initSub b u (rowPiece b N u) inf_le_right,
        hfinrank_N u]
    have htop_b : ∑ w ∈ M_col u, (Module.finrank K
          (piece b (⊤ : Submodule (MatPoly K n) (I → MatPoly K n)) u w) : ℤ) =
        (Module.finrank K (rowPiece b (⊤ : Submodule (MatPoly K n) (I → MatPoly K n)) u) : ℤ) := by
      rw [← Nat.cast_sum, sum_finrank_piece_top K b u]
    have htop_a : ∑ w ∈ M_col u, (Module.finrank K
          (piece a (⊤ : Submodule (MatPoly K n) (I → MatPoly K n)) u w) : ℤ) =
        (Module.finrank K (rowPiece a (⊤ : Submodule (MatPoly K n) (I → MatPoly K n)) u) : ℤ) := by
      rw [← Nat.cast_sum, sum_finrank_piece_top K a u]
    rw [hNs, htop_b, htop_a]
  refine ⟨Q, hQ_all, ?_⟩
  ext u
  rw [← evalAOneFun_polyToZaFun, hQ_eq, evalAOneFun_prodMulFactor, heval_H,
    prodRowMulFactor_sub, ← evalAOneFun_prodMulFactor, ← evalAOneFun_prodMulFactor,
    prodMulFactor_univ_HSeries_top_bot K b, prodMulFactor_univ_HSeries_top_bot K a]
  simp only [Pi.sub_apply, evalAOneFun_polyToZaFun, MvPolynomial.coeff_sub,
    MvPolynomial.coeff_sum]
  have hmap1 : ∀ (d : Fin n →₀ ℕ),
      evalAOne n (MvPolynomial.monomial d (1 : APoly n)) =
        MvPolynomial.monomial d (1 : ℤ) := by
    intro d
    unfold evalAOne
    rw [MvPolynomial.map_monomial, map_one]
  rw [map_sum, map_sum, MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
  simp_rw [hmap1]

end Bigraded

/-! ### Section 6: Koszul Block Matrix Recursion and Proof of Theorem 1.1 -/

def KoszulIdx {α : Type*} : List α → Type
  | [] => PUnit
  | _ :: tail => KoszulIdx tail ⊕ KoszulIdx tail

instance instFintypeKoszulIdx {α : Type*} : (l : List α) → Fintype (KoszulIdx l)
  | [] => inferInstanceAs (Fintype PUnit)
  | _ :: tail =>
    letI := instFintypeKoszulIdx tail
    inferInstanceAs (Fintype (KoszulIdx tail ⊕ KoszulIdx tail))

instance instDecidableEqKoszulIdx {α : Type*} : (l : List α) → DecidableEq (KoszulIdx l)
  | [] => inferInstanceAs (DecidableEq PUnit)
  | _ :: tail =>
    letI := instDecidableEqKoszulIdx tail
    inferInstanceAs (DecidableEq (KoszulIdx tail ⊕ KoszulIdx tail))

structure KoszulPack (K : Type*) [Field K] (n : ℕ)
    (head : Finset (Fin n) × MatPoly K n × MatPoly K n)
    (tail : List (Finset (Fin n) × MatPoly K n × MatPoly K n)) where
  A : Matrix (KoszulIdx tail) (KoszulIdx tail) (MatPoly K n)
  B : Matrix (KoszulIdx tail) (KoszulIdx tail) (MatPoly K n)
  a : KoszulIdx tail → (Fin n →₀ ℕ)
  b : KoszulIdx tail → (Fin n →₀ ℕ)

def buildKoszul {K : Type*} [Field K] {n : ℕ}
    (head : Finset (Fin n) × MatPoly K n × MatPoly K n) :
    (tail : List (Finset (Fin n) × MatPoly K n × MatPoly K n)) →
      KoszulPack K n head tail
  | [] =>
    { A := Matrix.of fun _ _ => head.2.1
      B := Matrix.of fun _ _ => head.2.2
      a := fun _ => indDeg head.1
      b := fun _ => 0 }
  | item :: tail =>
    let P0 := buildKoszul head tail
    { A := Matrix.fromBlocks P0.A (item.2.1 • 1) ((- item.2.2) • 1) P0.B
      B := Matrix.fromBlocks P0.B ((- item.2.1) • 1) (item.2.2 • 1) P0.A
      a := Sum.elim (fun q => P0.a q + oneDeg n) (fun p => P0.b p + oneDeg n + indDeg item.1)
      b := Sum.elim (fun p => P0.b p + oneDeg n) (fun q => P0.a q + indDeg item.1) }

def dotY {n : ℕ} (y : Fin n → ℂ) (u : Fin n →₀ ℕ) : ℂ :=
  ∑ i : Fin n, (u i : ℂ) * y i

lemma dotY_zero {n : ℕ} (y : Fin n → ℂ) : dotY y 0 = 0 := by
  simp [dotY]

lemma dotY_add {n : ℕ} (y : Fin n → ℂ) (u v : Fin n →₀ ℕ) :
    dotY y (u + v) = dotY y u + dotY y v := by
  unfold dotY
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Finsupp.add_apply, Nat.cast_add]; ring

lemma dotY_indDeg {n : ℕ} (y : Fin n → ℂ) (S : Finset (Fin n)) :
    dotY y (indDeg S) = ∑ i ∈ S, y i := by
  unfold dotY
  simp_rw [indDeg_apply]
  have : ∀ i : Fin n, ((if i ∈ S then (1 : ℕ) else 0 : ℕ) : ℂ) * y i =
      if i ∈ S then y i else 0 := by intro i; split_ifs <;> simp
  simp_rw [this, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

lemma buildKoszul_spec {K : Type*} [Field K] {n : ℕ}
    (head : Finset (Fin n) × MatPoly K n × MatPoly K n)
    (hhead_g : ∀ m ∈ head.2.1.support, rowDeg m = indDeg head.1)
    (hhead_h : ∀ m ∈ head.2.2.support, rowDeg m = indDeg (Finset.univ \ head.1))
    (tail : List (Finset (Fin n) × MatPoly K n × MatPoly K n))
    (htail : ∀ item ∈ tail,
      (∀ m ∈ item.2.1.support, rowDeg m = indDeg item.1) ∧
        (∀ m ∈ item.2.2.support, rowDeg m = indDeg (Finset.univ \ item.1))) :
    let P := buildKoszul head tail
    let f_sum : MatPoly K n :=
      ((tail ++ [head]).map (fun item => item.2.1 * item.2.2)).sum
    P.A * P.B = f_sum • 1 ∧
      P.B * P.A = f_sum • 1 ∧
      (∀ p q m, m ∈ (P.A p q).support → rowDeg m + P.b p = P.a q) ∧
      (∀ q p m, m ∈ (P.B q p).support → rowDeg m + P.a q = oneDeg n + P.b p) ∧
      (∀ (y : Fin n → ℂ), ∑ i : Fin n, y i = 0 → ∀ (Φ : Polynomial ℂ),
        ∑ p : KoszulIdx tail, (Φ.eval (dotY y (P.b p)) - Φ.eval (dotY y (P.a p))) =
          (iterDiff ((tail ++ [head]).map (fun item => ∑ i ∈ item.1, y i)) Φ).eval 0) := by
  induction tail with
  | nil =>
    dsimp only [buildKoszul]
    simp only [List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change (Matrix.of fun _ _ : PUnit => head.2.1) *
          (Matrix.of fun _ _ : PUnit => head.2.2) =
        (head.2.1 * head.2.2) • (1 : Matrix PUnit PUnit (MatPoly K n))
      ext ⟨⟩ ⟨⟩
      simp [Matrix.mul_apply]
    · change (Matrix.of fun _ _ : PUnit => head.2.2) *
          (Matrix.of fun _ _ : PUnit => head.2.1) =
        (head.2.1 * head.2.2) • (1 : Matrix PUnit PUnit (MatPoly K n))
      ext ⟨⟩ ⟨⟩
      simp [Matrix.mul_apply, mul_comm]
    · intro ⟨⟩ ⟨⟩ m hm
      exact hhead_g m hm
    · intro ⟨⟩ ⟨⟩ m hm
      rw [hhead_h m hm, add_comm, indDeg_add_sdiff]
    · intro y _ Φ
      change (∑ _p : PUnit, (Φ.eval (dotY y 0) - Φ.eval (dotY y (indDeg head.1)))) =
        (iterDiff [∑ i ∈ head.1, y i] Φ).eval 0
      have hsum : (∑ _p : PUnit, (Φ.eval (dotY y 0) - Φ.eval (dotY y (indDeg head.1)))) =
          Φ.eval (dotY y 0) - Φ.eval (dotY y (indDeg head.1)) := by simp
      rw [hsum, dotY_zero, dotY_indDeg]
      simp [iterDiff, eval_diffOp]
  | cons item tail ih =>
    have hitem := htail item List.mem_cons_self
    have htail' : ∀ x ∈ tail,
        (∀ m ∈ x.2.1.support, rowDeg m = indDeg x.1) ∧
          (∀ m ∈ x.2.2.support, rowDeg m = indDeg (Finset.univ \ x.1)) :=
      fun x hx => htail x (List.mem_cons_of_mem _ hx)
    rcases ih htail' with ⟨hAB, hBA, hA_deg, hB_deg, hdiff⟩
    set P0 := buildKoszul head tail
    set f0 : MatPoly K n := ((tail ++ [head]).map (fun x => x.2.1 * x.2.2)).sum
    dsimp only [buildKoszul, List.cons_append, List.map_cons, List.sum_cons]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- `A' * B' = (item.g * item.h + f0) • 1`
      change Matrix.fromBlocks P0.A (item.2.1 • 1) ((-item.2.2) • 1) P0.B *
          Matrix.fromBlocks P0.B ((-item.2.1) • 1) (item.2.2 • 1) P0.A =
        (item.2.1 * item.2.2 + f0) •
          (1 : Matrix (KoszulIdx tail ⊕ KoszulIdx tail) (KoszulIdx tail ⊕ KoszulIdx tail) _)
      rw [Matrix.fromBlocks_multiply]
      have h11 : P0.A * P0.B + (item.2.1 • (1 : Matrix (KoszulIdx tail) _ _)) *
          (item.2.2 • 1) = (item.2.1 * item.2.2 + f0) • 1 := by
        rw [hAB, smul_mul_smul_comm, one_mul, ← add_smul, add_comm]
      have h12 : P0.A * ((-item.2.1) • (1 : Matrix (KoszulIdx tail) _ _)) +
          (item.2.1 • 1) * P0.A = 0 := by
        rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul, neg_smul, neg_add_cancel]
      have h21 : ((-item.2.2) • (1 : Matrix (KoszulIdx tail) _ _)) * P0.B +
          P0.B * (item.2.2 • 1) = 0 := by
        rw [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, neg_smul, neg_add_cancel]
      have h22 : ((-item.2.2) • (1 : Matrix (KoszulIdx tail) _ _)) * ((-item.2.1) • 1) +
          P0.B * P0.A = (item.2.1 * item.2.2 + f0) • 1 := by
        rw [hBA, smul_mul_smul_comm, one_mul, neg_mul_neg, mul_comm item.2.2, ← add_smul]
      rw [h11, h12, h21, h22]
      funext i j
      rcases i with i | i <;> rcases j with j | j
      · by_cases hij : i = j
        · subst hij
          change (item.2.1 * item.2.2 + f0) *
              (1 : Matrix (KoszulIdx tail) (KoszulIdx tail) (MatPoly K n)) i i =
            (item.2.1 * item.2.2 + f0) *
              (1 : Matrix (KoszulIdx tail ⊕ KoszulIdx tail) (KoszulIdx tail ⊕ KoszulIdx tail)
                (MatPoly K n)) (Sum.inl i) (Sum.inl i)
          rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
        · have hinl : (Sum.inl i : KoszulIdx tail ⊕ KoszulIdx tail) ≠ Sum.inl j :=
            fun h => hij (Sum.inl.inj h)
          change (item.2.1 * item.2.2 + f0) *
              (1 : Matrix (KoszulIdx tail) (KoszulIdx tail) (MatPoly K n)) i j =
            (item.2.1 * item.2.2 + f0) *
              (1 : Matrix (KoszulIdx tail ⊕ KoszulIdx tail) (KoszulIdx tail ⊕ KoszulIdx tail)
                (MatPoly K n)) (Sum.inl i) (Sum.inl j)
          rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hinl]
      · have hne : (Sum.inl i : KoszulIdx tail ⊕ KoszulIdx tail) ≠ Sum.inr j := by simp
        change (0 : MatPoly K n) =
          (item.2.1 * item.2.2 + f0) *
            (1 : Matrix (KoszulIdx tail ⊕ KoszulIdx tail) (KoszulIdx tail ⊕ KoszulIdx tail)
              (MatPoly K n)) (Sum.inl i) (Sum.inr j)
        rw [Matrix.one_apply_ne hne, mul_zero]
      · have hne : (Sum.inr i : KoszulIdx tail ⊕ KoszulIdx tail) ≠ Sum.inl j := by simp
        change (0 : MatPoly K n) =
          (item.2.1 * item.2.2 + f0) *
            (1 : Matrix (KoszulIdx tail ⊕ KoszulIdx tail) (KoszulIdx tail ⊕ KoszulIdx tail)
              (MatPoly K n)) (Sum.inr i) (Sum.inl j)
        rw [Matrix.one_apply_ne hne, mul_zero]
      · by_cases hij : i = j
        · subst hij
          change (item.2.1 * item.2.2 + f0) *
              (1 : Matrix (KoszulIdx tail) (KoszulIdx tail) (MatPoly K n)) i i =
            (item.2.1 * item.2.2 + f0) *
              (1 : Matrix (KoszulIdx tail ⊕ KoszulIdx tail) (KoszulIdx tail ⊕ KoszulIdx tail)
                (MatPoly K n)) (Sum.inr i) (Sum.inr i)
          rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
        · have hinr : (Sum.inr i : KoszulIdx tail ⊕ KoszulIdx tail) ≠ Sum.inr j :=
            fun h => hij (Sum.inr.inj h)
          change (item.2.1 * item.2.2 + f0) *
              (1 : Matrix (KoszulIdx tail) (KoszulIdx tail) (MatPoly K n)) i j =
            (item.2.1 * item.2.2 + f0) *
              (1 : Matrix (KoszulIdx tail ⊕ KoszulIdx tail) (KoszulIdx tail ⊕ KoszulIdx tail)
                (MatPoly K n)) (Sum.inr i) (Sum.inr j)
          rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hinr]
    · -- `B' * A' = (item.g * item.h + f0) • 1`
      change Matrix.fromBlocks P0.B ((-item.2.1) • 1) (item.2.2 • 1) P0.A *
          Matrix.fromBlocks P0.A (item.2.1 • 1) ((-item.2.2) • 1) P0.B =
        (item.2.1 * item.2.2 + f0) •
          (1 : Matrix (KoszulIdx tail ⊕ KoszulIdx tail) (KoszulIdx tail ⊕ KoszulIdx tail) _)
      rw [Matrix.fromBlocks_multiply]
      have h11 : P0.B * P0.A + ((-item.2.1) • (1 : Matrix (KoszulIdx tail) _ _)) *
          ((-item.2.2) • 1) = (item.2.1 * item.2.2 + f0) • 1 := by
        rw [hBA, smul_mul_smul_comm, one_mul, neg_mul_neg, ← add_smul, add_comm]
      have h12 : P0.B * (item.2.1 • (1 : Matrix (KoszulIdx tail) _ _)) +
          ((-item.2.1) • 1) * P0.B = 0 := by
        rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul, neg_smul, add_neg_cancel]
      have h21 : (item.2.2 • (1 : Matrix (KoszulIdx tail) _ _)) * P0.A +
          P0.A * ((-item.2.2) • 1) = 0 := by
        rw [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, neg_smul, add_neg_cancel]
      have h22 : (item.2.2 • (1 : Matrix (KoszulIdx tail) _ _)) * (item.2.1 • 1) +
          P0.A * P0.B = (item.2.1 * item.2.2 + f0) • 1 := by
        rw [hAB, smul_mul_smul_comm, one_mul, mul_comm item.2.2, ← add_smul]
      rw [h11, h12, h21, h22]
      funext i j
      rcases i with i | i <;> rcases j with j | j
      · by_cases hij : i = j
        · subst hij
          change (item.2.1 * item.2.2 + f0) *
              (1 : Matrix (KoszulIdx tail) (KoszulIdx tail) (MatPoly K n)) i i =
            (item.2.1 * item.2.2 + f0) *
              (1 : Matrix (KoszulIdx tail ⊕ KoszulIdx tail) (KoszulIdx tail ⊕ KoszulIdx tail)
                (MatPoly K n)) (Sum.inl i) (Sum.inl i)
          rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
        · have hinl : (Sum.inl i : KoszulIdx tail ⊕ KoszulIdx tail) ≠ Sum.inl j :=
            fun h => hij (Sum.inl.inj h)
          change (item.2.1 * item.2.2 + f0) *
              (1 : Matrix (KoszulIdx tail) (KoszulIdx tail) (MatPoly K n)) i j =
            (item.2.1 * item.2.2 + f0) *
              (1 : Matrix (KoszulIdx tail ⊕ KoszulIdx tail) (KoszulIdx tail ⊕ KoszulIdx tail)
                (MatPoly K n)) (Sum.inl i) (Sum.inl j)
          rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hinl]
      · have hne : (Sum.inl i : KoszulIdx tail ⊕ KoszulIdx tail) ≠ Sum.inr j := by simp
        change (0 : MatPoly K n) =
          (item.2.1 * item.2.2 + f0) *
            (1 : Matrix (KoszulIdx tail ⊕ KoszulIdx tail) (KoszulIdx tail ⊕ KoszulIdx tail)
              (MatPoly K n)) (Sum.inl i) (Sum.inr j)
        rw [Matrix.one_apply_ne hne, mul_zero]
      · have hne : (Sum.inr i : KoszulIdx tail ⊕ KoszulIdx tail) ≠ Sum.inl j := by simp
        change (0 : MatPoly K n) =
          (item.2.1 * item.2.2 + f0) *
            (1 : Matrix (KoszulIdx tail ⊕ KoszulIdx tail) (KoszulIdx tail ⊕ KoszulIdx tail)
              (MatPoly K n)) (Sum.inr i) (Sum.inl j)
        rw [Matrix.one_apply_ne hne, mul_zero]
      · by_cases hij : i = j
        · subst hij
          change (item.2.1 * item.2.2 + f0) *
              (1 : Matrix (KoszulIdx tail) (KoszulIdx tail) (MatPoly K n)) i i =
            (item.2.1 * item.2.2 + f0) *
              (1 : Matrix (KoszulIdx tail ⊕ KoszulIdx tail) (KoszulIdx tail ⊕ KoszulIdx tail)
                (MatPoly K n)) (Sum.inr i) (Sum.inr i)
          rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
        · have hinr : (Sum.inr i : KoszulIdx tail ⊕ KoszulIdx tail) ≠ Sum.inr j :=
            fun h => hij (Sum.inr.inj h)
          change (item.2.1 * item.2.2 + f0) *
              (1 : Matrix (KoszulIdx tail) (KoszulIdx tail) (MatPoly K n)) i j =
            (item.2.1 * item.2.2 + f0) *
              (1 : Matrix (KoszulIdx tail ⊕ KoszulIdx tail) (KoszulIdx tail ⊕ KoszulIdx tail)
                (MatPoly K n)) (Sum.inr i) (Sum.inr j)
          rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hinr]
    · -- Degree of `A'`
      rintro (p | q') (q | p') m hm
      · dsimp only [Matrix.fromBlocks_apply₁₁, Sum.elim_inl] at hm ⊢
        rw [← add_assoc, hA_deg p q m hm]
      · dsimp only [Matrix.fromBlocks_apply₁₂, Sum.elim_inl, Sum.elim_inr] at hm ⊢
        by_cases hpp' : p = p'
        · subst hpp'
          simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hm
          rw [hitem.1 m hm]; abel
        · simp only [Matrix.smul_apply, Matrix.one_apply_ne hpp', smul_zero,
            MvPolynomial.support_zero] at hm
          exact False.elim (Finset.notMem_empty m hm)
      · dsimp only [Matrix.fromBlocks_apply₂₁, Sum.elim_inr, Sum.elim_inl] at hm ⊢
        by_cases hq'q : q' = q
        · subst hq'q
          simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
            MvPolynomial.support_neg] at hm
          rw [hitem.2 m hm]
          calc indDeg (Finset.univ \ item.1) + (P0.a q' + indDeg item.1)
              = P0.a q' + (indDeg item.1 + indDeg (Finset.univ \ item.1)) := by abel
            _ = P0.a q' + oneDeg n := by rw [indDeg_add_sdiff]
        · simp only [Matrix.smul_apply, Matrix.one_apply_ne hq'q, smul_zero,
            MvPolynomial.support_zero] at hm
          exact False.elim (Finset.notMem_empty m hm)
      · dsimp only [Matrix.fromBlocks_apply₂₂, Sum.elim_inr] at hm ⊢
        have hb := hB_deg q' p' m hm
        calc rowDeg m + (P0.a q' + indDeg item.1)
            = (rowDeg m + P0.a q') + indDeg item.1 := by abel
          _ = (oneDeg n + P0.b p') + indDeg item.1 := by rw [hb]
          _ = P0.b p' + oneDeg n + indDeg item.1 := by abel
    · -- Degree of `B'`
      rintro (q | p') (p | q') m hm
      · dsimp only [Matrix.fromBlocks_apply₁₁, Sum.elim_inl] at hm ⊢
        have hb := hB_deg q p m hm
        calc rowDeg m + (P0.a q + oneDeg n)
            = (rowDeg m + P0.a q) + oneDeg n := by abel
          _ = (oneDeg n + P0.b p) + oneDeg n := by rw [hb]
          _ = oneDeg n + (P0.b p + oneDeg n) := by abel
      · dsimp only [Matrix.fromBlocks_apply₁₂, Sum.elim_inl, Sum.elim_inr] at hm ⊢
        by_cases hqq' : q = q'
        · subst hqq'
          simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
            MvPolynomial.support_neg] at hm
          rw [hitem.1 m hm]; abel
        · simp only [Matrix.smul_apply, Matrix.one_apply_ne hqq', smul_zero,
            MvPolynomial.support_zero] at hm
          exact False.elim (Finset.notMem_empty m hm)
      · dsimp only [Matrix.fromBlocks_apply₂₁, Sum.elim_inr, Sum.elim_inl] at hm ⊢
        by_cases hp'p : p' = p
        · subst hp'p
          simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hm
          rw [hitem.2 m hm]
          calc indDeg (Finset.univ \ item.1) + (P0.b p' + oneDeg n + indDeg item.1)
              = (indDeg item.1 + indDeg (Finset.univ \ item.1)) + (P0.b p' + oneDeg n) := by abel
            _ = oneDeg n + (P0.b p' + oneDeg n) := by rw [indDeg_add_sdiff]
        · simp only [Matrix.smul_apply, Matrix.one_apply_ne hp'p, smul_zero,
            MvPolynomial.support_zero] at hm
          exact False.elim (Finset.notMem_empty m hm)
      · dsimp only [Matrix.fromBlocks_apply₂₂, Sum.elim_inr] at hm ⊢
        have ha := hA_deg p' q' m hm
        calc rowDeg m + (P0.b p' + oneDeg n + indDeg item.1)
            = oneDeg n + ((rowDeg m + P0.b p') + indDeg item.1) := by abel
          _ = oneDeg n + (P0.a q' + indDeg item.1) := by rw [ha]
    · -- Finite difference identity
      intro y hy0 Φ
      have hone0 : dotY y (oneDeg n) = 0 := by
        rw [oneDeg, dotY_indDeg]
        simpa using hy0
      change (∑ p : KoszulIdx tail ⊕ KoszulIdx tail,
          (Φ.eval (dotY y (Sum.elim (fun p => P0.b p + oneDeg n) (fun q => P0.a q + indDeg item.1) p)) -
            Φ.eval (dotY y (Sum.elim (fun q => P0.a q + oneDeg n) (fun p => P0.b p + oneDeg n + indDeg item.1) p)))) = _
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, dotY_add, hone0, add_zero, dotY_indDeg]
      set t₁ : ℂ := ∑ i ∈ item.1, y i
      have hcombine : (∑ x : KoszulIdx tail,
            (Φ.eval (dotY y (P0.b x)) - Φ.eval (dotY y (P0.a x)))) +
          (∑ x : KoszulIdx tail,
            (Φ.eval (dotY y (P0.a x) + t₁) - Φ.eval (dotY y (P0.b x) + t₁))) =
          ∑ x : KoszulIdx tail,
            ((diffOp t₁ Φ).eval (dotY y (P0.b x)) -
              (diffOp t₁ Φ).eval (dotY y (P0.a x))) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [eval_diffOp, eval_diffOp]
        ring
      rw [hcombine, hdiff y hy0 (diffOp t₁ Φ)]
      rfl

theorem theorem_1_1_proof {K : Type*} [Field K] {n : ℕ}
    (hn : 2 < n) (c : Equiv.Perm (Fin n) → Kˣ) :
    (if Odd n then (n : ℕ∞) else ((n - 1 : ℕ) : ℕ∞)) ≤
      DetSupportRank.DeterminantSupport.partitionRank
        (DetSupportRank.DeterminantSupport.determinantSupportPolynomial c) := by
  set target : ℕ := if Odd n then n else n - 1
  have hcast : (if Odd n then (n : ℕ∞) else ((n - 1 : ℕ) : ℕ∞)) = (target : ℕ∞) := by
    dsimp [target]; split_ifs <;> rfl
  rw [hcast]
  unfold DetSupportRank.DeterminantSupport.partitionRank
  refine le_iInf (fun ⟨r, hr_decomp⟩ => ?_)
  rw [Nat.cast_le]
  by_contra hlt_not
  have hr_lt : r < target := Nat.lt_of_not_ge hlt_not
  have hr_lt_n : r < n := by
    dsimp [target] at hr_lt; split_ifs at hr_lt <;> omega
  set D := DetSupportRank.DeterminantSupport.determinantSupportPolynomial c
  rcases hr_decomp with ⟨S, g, h, hSgh, hD_eq⟩
  -- Rule out `r = 0`:
  rcases Nat.eq_zero_or_pos r with rfl | hr_pos
  · simp only [Finset.univ_eq_empty, Finset.sum_empty] at hD_eq
    exact D_ne_zero c hD_eq
  -- Write `r = m + 1`:
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr_pos)
  set head : Finset (Fin n) × MatPoly K n × MatPoly K n := (S 0, g 0, h 0)
  set tail : List (Finset (Fin n) × MatPoly K n × MatPoly K n) :=
    (List.finRange m).map (fun j : Fin m => (S j.succ, g j.succ, h j.succ))
  have hhead_g : ∀ m_exp ∈ head.2.1.support, rowDeg m_exp = indDeg head.1 :=
    fun m_exp hm => rowDeg_eq_indDeg_of_setMultilinear (hSgh 0).2.2.1 hm
  have hhead_h : ∀ m_exp ∈ head.2.2.support, rowDeg m_exp = indDeg (Finset.univ \ head.1) :=
    fun m_exp hm => rowDeg_eq_indDeg_of_setMultilinear (hSgh 0).2.2.2 hm
  have htail : ∀ item ∈ tail,
      (∀ m_exp ∈ item.2.1.support, rowDeg m_exp = indDeg item.1) ∧
        (∀ m_exp ∈ item.2.2.support, rowDeg m_exp = indDeg (Finset.univ \ item.1)) := by
    intro item hitem
    rcases List.mem_map.mp hitem with ⟨j, _, rfl⟩
    exact ⟨fun m_exp hm => rowDeg_eq_indDeg_of_setMultilinear (hSgh j.succ).2.2.1 hm,
      fun m_exp hm => rowDeg_eq_indDeg_of_setMultilinear (hSgh j.succ).2.2.2 hm⟩
  set KP := buildKoszul head tail
  have hspec := buildKoszul_spec head hhead_g hhead_h tail htail
  have hf_sum_eq_D : ((tail ++ [head]).map (fun item => item.2.1 * item.2.2)).sum = D := by
    rw [List.map_append, List.sum_append]
    simp only [tail, head, List.map_map, Function.comp_def, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    rw [← Fin.sum_univ_def, add_comm, hD_eq, Fin.sum_univ_succ]
  rw [hf_sum_eq_D] at hspec
  rcases hspec with ⟨hAB, hBA, hA_deg, _, hdiff⟩
  -- Obtain `Q : ZaPoly n` in `⋂_τ JIdeal τ` with `evalAOne n Q = ∑ z^(b p) - ∑ z^(a q)`:
  obtain ⟨Q, hQ_mem, hQ_eval⟩ := exists_JIdeal_poly_of_koszul_pair c KP.A KP.B KP.a KP.b
    hAB hBA hA_deg
  -- Find a permutation `π : Equiv.Perm (Fin n)` avoiding all `r = m + 1` hyperplanes `S k`:
  obtain ⟨π, hπ⟩ := exists_perm_avoiding_hyperplanes hn hr_lt S
    (fun k => ⟨(hSgh k).1, (hSgh k).2.1⟩)
  set y : Fin n → ℂ := fun i => root n (π i)
  have hy_sum0 : ∑ i : Fin n, y i = 0 := by
    dsimp [y]
    rw [Equiv.sum_comp π (root n)]
    exact sum_univ_root (by omega)
  -- On one hand, `evalPow y (m + 1) (evalAOne n Q) = 0`:
  have hzero : evalPow y (m + 1) (evalAOne n Q) = 0 :=
    evalPow_evalAOne_eq_zero (by omega) hr_lt_n π hQ_mem
  -- On the other hand, `evalPow y (m + 1) (evalAOne n Q)` equals the nonzero finite difference!
  have heval_diff : evalPow y (m + 1) (evalAOne n Q) =
      ∑ p : KoszulIdx tail,
        ((Polynomial.X ^ (m + 1) : Polynomial ℂ).eval (dotY y (KP.b p)) -
          (Polynomial.X ^ (m + 1) : Polynomial ℂ).eval (dotY y (KP.a p))) := by
    rw [hQ_eval, map_sub, map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [evalPow_monomial, evalPow_monomial]
    simp [dotY]
  set ts : List ℂ := (tail ++ [head]).map (fun item => ∑ i ∈ item.1, y i)
  have hts_len : ts.length = m + 1 := by
    simp [ts, tail]
  have hts_prod : ts.prod = ∏ k : Fin (m + 1), (∑ i ∈ S k, y i) := by
    simp only [ts, List.map_append, List.prod_append, tail, head, List.map_map,
      Function.comp_def, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [← Fin.prod_univ_def, mul_comm, Fin.prod_univ_succ]
  rw [heval_diff, hdiff y hy_sum0 (Polynomial.X ^ (m + 1)), ← hts_len, iterDiff_X_pow ts,
    Polynomial.eval_C, hts_len, hts_prod] at hzero
  have hnonzero : (-1 : ℂ) ^ (m + 1) * ((m + 1).factorial : ℂ) *
      (∏ k : Fin (m + 1), ∑ i ∈ S k, y i) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_) ?_
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    · rw [Finset.prod_ne_zero_iff]
      intro k _
      exact hπ k
  exact hnonzero hzero

end DetSupportRank_Proof

open DetSupportRank.DeterminantSupport

theorem solution {K : Type*} [Field K] {n : ℕ}
    (hn : 2 < n) (c : Equiv.Perm (Fin n) → Kˣ) :
    (if Odd n then (n : ℕ∞) else ((n - 1 : ℕ) : ℕ∞)) ≤
      partitionRank (determinantSupportPolynomial c) :=
  DetSupportRank_Proof.theorem_1_1_proof hn c
