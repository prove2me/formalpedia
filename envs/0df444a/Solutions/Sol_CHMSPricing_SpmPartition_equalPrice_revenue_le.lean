-- Prove2me | solution 1 for CHMSPricing.SpmPartition.equalPrice_revenue_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T03:52:25.731986+00:00
-- url     : https://prove2.me/submissions/dd4cb238-f00f-4623-82d3-026b9ac39a0f

import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_Spm

set_option autoImplicit false

open CHMSPricing.SpmPartition in
lemma oneUnitOfferProb_nonneg_138e {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (k : Fin n) : 0 ≤ oneUnitOfferProb q k := by
  unfold oneUnitOfferProb
  exact Finset.prod_nonneg fun j _ => by linarith [(hq j).2]

open CHMSPricing.SpmPartition in
lemma oneUnitOfferProb_anti_138e {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    {i j : Fin n} (hij : i ≤ j) : oneUnitOfferProb q j ≤ oneUnitOfferProb q i := by
  unfold oneUnitOfferProb
  have hsub : Finset.univ.filter (· < i) ⊆ Finset.univ.filter (· < j) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact lt_of_lt_of_le hx hij
  rw [← Finset.prod_sdiff hsub]
  have h1 : ∏ x ∈ Finset.univ.filter (· < j) \ Finset.univ.filter (· < i), (1 - q x) ≤ 1 :=
    Finset.prod_le_one (fun x _ => by linarith [(hq x).2]) (fun x _ => by linarith [(hq x).1])
  have h0 : 0 ≤ ∏ x ∈ Finset.univ.filter (· < i), (1 - q x) :=
    Finset.prod_nonneg fun x _ => by linarith [(hq x).2]
  calc (∏ x ∈ Finset.univ.filter (· < j) \ Finset.univ.filter (· < i), (1 - q x)) *
        ∏ x ∈ Finset.univ.filter (· < i), (1 - q x)
      ≤ 1 * ∏ x ∈ Finset.univ.filter (· < i), (1 - q x) :=
        mul_le_mul_of_nonneg_right h1 h0
    _ = _ := one_mul _

lemma weighted_sign_change_138e {n : ℕ} (c q pr : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hpr : Antitone pr) (hc0 : ∀ i, 0 ≤ c i)
    (hc : ∀ i j : Fin n, i ≤ j → c j ≤ c i)
    (pbar : ℝ) (h2 : ∑ i, pr i * q i = pbar * ∑ i, q i) :
    0 ≤ ∑ i, c i * (q i * (pr i - pbar)) := by
  classical
  set T := Finset.univ.filter (fun j : Fin n => pr j < pbar) with hT
  -- threshold t
  obtain ⟨t, ht_lo, ht_hi⟩ : ∃ t : ℝ, (∀ j ∈ T, c j ≤ t) ∧
      (∀ i : Fin n, pbar ≤ pr i → t ≤ c i) := by
    by_cases hne : T.Nonempty
    · refine ⟨T.sup' hne c, fun j hj => Finset.le_sup' c hj, ?_⟩
      intro i hi
      rw [Finset.sup'_le_iff]
      intro j hj
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      apply hc
      by_contra hji
      rw [not_le] at hji
      have := hpr hji.le
      linarith
    · refine ⟨0, fun j hj => absurd ⟨j, hj⟩ hne, fun i _ => hc0 i⟩
  have hsum0 : ∑ i, q i * (pr i - pbar) = 0 := by
    have : ∑ i, q i * (pr i - pbar) = ∑ i, pr i * q i - pbar * ∑ i, q i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, h2, sub_self]
  have hdecomp : ∑ i, c i * (q i * (pr i - pbar)) =
      ∑ i, (c i - t) * (q i * (pr i - pbar)) + t * ∑ i, q i * (pr i - pbar) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hdecomp, hsum0, mul_zero, add_zero]
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : pbar ≤ pr i
  · exact mul_nonneg (by linarith [ht_hi i hi]) (mul_nonneg (hq i) (by linarith))
  · rw [not_le] at hi
    have hiT : i ∈ T := by simp [hT, hi]
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith [ht_lo i hiT])
      (mul_nonpos_of_nonneg_of_nonpos (hq i) (by linarith))

open CHMSPricing.SpmPartition in
theorem solution {n : ℕ} (q pr : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hpr : Antitone pr)
    (pbar : ℝ) (h2 : ∑ i, pr i * q i = pbar * ∑ i, q i) :
    pbar * ∑ i, oneUnitOfferProb q i * q i ≤ ∑ i, oneUnitOfferProb q i * pr i * q i := by
  have key := weighted_sign_change_138e (oneUnitOfferProb q) q pr (fun i => (hq i).1) hpr
    (oneUnitOfferProb_nonneg_138e q hq) (fun i j hij => oneUnitOfferProb_anti_138e q hq hij)
    pbar h2
  have : ∑ i, oneUnitOfferProb q i * pr i * q i - pbar * ∑ i, oneUnitOfferProb q i * q i =
      ∑ i, oneUnitOfferProb q i * (q i * (pr i - pbar)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith
