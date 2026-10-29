-- Prove2me | solution 1 for GaoImpatientMNL.Pricing.lemma_C_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-29T04:56:58.599989+00:00
-- url     : https://prove2.me/submissions/e8e95d01-434b-4113-b166-77be168bcc05

import Mathlib
import Definitions.Def_GaoImpatientMNL_Pricing_Model

open scoped BigOperators

namespace GaoImpatientMNL.Pricing.Attempt

open GaoImpatientMNL.Pricing

def clipPrices {n : ℕ} (p : Fin n → ℝ) : Fin n → ℝ := fun i => max 0 (p i)

noncomputable def stageNumerator {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k : Fin m) : ℝ :=
  ∑ i ∈ S k, p i * Real.exp (α i - β * p i)

noncomputable def stageDenominator {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k : Fin m) : ℝ :=
  (1 + prefixWeight (fun i => Real.exp (α i - β * p i)) S k) *
    (1 + prefixWeight (fun i => Real.exp (α i - β * p i)) S k + attraction α β p (S k))

noncomputable def stageRevenue {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k : Fin m) : ℝ :=
  lam k * stageNumerator α β S p k / stageDenominator α β S p k

theorem revenue_eq_stageRevenue {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) :
    revenue α β lam S p = ∑ k, stageRevenue α β lam S p k := by
  rfl

theorem clipped_exp_le {n : ℕ} (α : Fin n → ℝ) (β : ℝ) (p : Fin n → ℝ)
    (hβ : 0 < β) (i : Fin n) :
    Real.exp (α i - β * clipPrices p i) ≤ Real.exp (α i - β * p i) := by
  apply Real.exp_le_exp.mpr
  have hp : p i ≤ clipPrices p i := le_max_right 0 (p i)
  nlinarith

theorem clipped_price_term_le {n : ℕ} (α : Fin n → ℝ) (β : ℝ) (p : Fin n → ℝ)
    (i : Fin n) :
    p i * Real.exp (α i - β * p i) ≤
      clipPrices p i * Real.exp (α i - β * clipPrices p i) := by
  by_cases hneg : p i < 0
  · simp [clipPrices, max_eq_left (le_of_lt hneg)]
    have he : 0 < Real.exp (α i - β * p i) := Real.exp_pos _
    nlinarith
  · have hp : 0 ≤ p i := le_of_not_gt hneg
    simp [clipPrices, max_eq_right hp]

theorem clipped_price_term_nonneg {n : ℕ} (α : Fin n → ℝ) (β : ℝ) (p : Fin n → ℝ)
    (i : Fin n) :
    0 ≤ clipPrices p i * Real.exp (α i - β * clipPrices p i) := by
  apply mul_nonneg
  · exact le_max_left 0 (p i)
  · exact le_of_lt (Real.exp_pos _)

theorem clipped_price_term_lt_of_neg {n : ℕ} (α : Fin n → ℝ) (β : ℝ) (p : Fin n → ℝ)
    (i : Fin n) (hneg : p i < 0) :
    p i * Real.exp (α i - β * p i) <
      clipPrices p i * Real.exp (α i - β * clipPrices p i) := by
  simp [clipPrices, max_eq_left (le_of_lt hneg)]
  exact mul_neg_of_neg_of_pos hneg (Real.exp_pos _)

theorem attraction_clip_le {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k : Fin m) (hβ : 0 < β) :
    attraction α β (clipPrices p) (S k) ≤ attraction α β p (S k) := by
  unfold attraction
  apply Finset.sum_le_sum
  intro i hi
  exact clipped_exp_le α β p hβ i

theorem prefix_clip_le {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k : Fin m) (hβ : 0 < β) :
    prefixWeight (fun i => Real.exp (α i - β * clipPrices p i)) S k ≤
      prefixWeight (fun i => Real.exp (α i - β * p i)) S k := by
  unfold prefixWeight
  apply Finset.sum_le_sum
  intro h hh
  apply Finset.sum_le_sum
  intro i hi
  exact clipped_exp_le α β p hβ i

theorem stageNumerator_clip_le {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k : Fin m) :
    stageNumerator α β S p k ≤ stageNumerator α β S (clipPrices p) k := by
  unfold stageNumerator
  apply Finset.sum_le_sum
  intro i hi
  exact clipped_price_term_le α β p i

theorem stageNumerator_clip_nonneg {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k : Fin m) :
    0 ≤ stageNumerator α β S (clipPrices p) k := by
  unfold stageNumerator
  apply Finset.sum_nonneg
  intro i hi
  exact clipped_price_term_nonneg α β p i

theorem stageNumerator_clip_lt {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k : Fin m) (i : Fin n)
    (hi : i ∈ S k) (hneg : p i < 0) :
    stageNumerator α β S p k < stageNumerator α β S (clipPrices p) k := by
  unfold stageNumerator
  apply Finset.sum_lt_sum
  · intro j hj
    exact clipped_price_term_le α β p j
  · exact ⟨i, hi, clipped_price_term_lt_of_neg α β p i hneg⟩

theorem stageDenominator_clip_le {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k : Fin m) (hβ : 0 < β) :
    stageDenominator α β S (clipPrices p) k ≤ stageDenominator α β S p k := by
  unfold stageDenominator
  have hW := prefix_clip_le α β S p k hβ
  have hV := attraction_clip_le α β S p k hβ
  have hW0 : 0 ≤ prefixWeight (fun i => Real.exp (α i - β * clipPrices p i)) S k := by
    unfold prefixWeight
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro i hi
    exact le_of_lt (Real.exp_pos _)
  have hW' : 0 ≤ prefixWeight (fun i => Real.exp (α i - β * p i)) S k := by
    unfold prefixWeight
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro i hi
    exact le_of_lt (Real.exp_pos _)
  have hV0 : 0 ≤ attraction α β (clipPrices p) (S k) := by
    unfold attraction
    apply Finset.sum_nonneg
    intro i hi
    exact le_of_lt (Real.exp_pos _)
  have hA : 1 + prefixWeight (fun i => Real.exp (α i - β * clipPrices p i)) S k ≤
      1 + prefixWeight (fun i => Real.exp (α i - β * p i)) S k := by linarith
  have hB : 1 + prefixWeight (fun i => Real.exp (α i - β * clipPrices p i)) S k +
      attraction α β (clipPrices p) (S k) ≤
      1 + prefixWeight (fun i => Real.exp (α i - β * p i)) S k + attraction α β p (S k) := by
    linarith
  have hB0 : 0 ≤ 1 + prefixWeight (fun i => Real.exp (α i - β * clipPrices p i)) S k +
      attraction α β (clipPrices p) (S k) := by linarith
  have hA1 : 0 ≤ 1 + prefixWeight (fun i => Real.exp (α i - β * p i)) S k := by linarith
  exact mul_le_mul hA hB hB0 hA1

theorem stageDenominator_pos {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k : Fin m) :
    0 < stageDenominator α β S p k := by
  unfold stageDenominator prefixWeight attraction
  positivity

theorem ratio_clip_le (wgt N N0 D D0 : ℝ)
    (hwgt : 0 < wgt) (hN : N ≤ N0) (hN0 : 0 ≤ N0)
    (hD : 0 < D) (hD0 : 0 < D0) (hDD0 : D0 ≤ D) :
    wgt * N / D ≤ wgt * N0 / D0 := by
  by_cases hNpos : 0 ≤ N
  · have hnum : wgt * N ≤ wgt * N0 := mul_le_mul_of_nonneg_left hN (le_of_lt hwgt)
    have hnum0 : 0 ≤ wgt * N0 := mul_nonneg (le_of_lt hwgt) hN0
    rw [div_le_div_iff₀ hD hD0]
    calc
      (wgt * N) * D0 ≤ (wgt * N0) * D0 := mul_le_mul_of_nonneg_right hnum (le_of_lt hD0)
      _ ≤ (wgt * N0) * D := mul_le_mul_of_nonneg_left hDD0 hnum0
  · have hnum : wgt * N < 0 := mul_neg_of_pos_of_neg hwgt (lt_of_not_ge hNpos)
    have hleft : wgt * N / D < 0 := div_neg_of_neg_of_pos hnum hD
    have hright : 0 ≤ wgt * N0 / D0 := div_nonneg (mul_nonneg (le_of_lt hwgt) hN0) (le_of_lt hD0)
    linarith

theorem ratio_clip_lt (wgt N N0 D D0 : ℝ)
    (hwgt : 0 < wgt) (hN : N < N0) (hN0 : 0 ≤ N0)
    (hD : 0 < D) (hD0 : 0 < D0) (hDD0 : D0 ≤ D) :
    wgt * N / D < wgt * N0 / D0 := by
  by_cases hNpos : 0 ≤ N
  · have hnum : wgt * N < wgt * N0 := mul_lt_mul_of_pos_left hN hwgt
    have hnum0 : 0 ≤ wgt * N0 := mul_nonneg (le_of_lt hwgt) hN0
    rw [div_lt_div_iff₀ hD hD0]
    calc
      (wgt * N) * D0 < (wgt * N0) * D0 := mul_lt_mul_of_pos_right hnum hD0
      _ ≤ (wgt * N0) * D := mul_le_mul_of_nonneg_left hDD0 hnum0
  · have hnum : wgt * N < 0 := mul_neg_of_pos_of_neg hwgt (lt_of_not_ge hNpos)
    have hleft : wgt * N / D < 0 := div_neg_of_neg_of_pos hnum hD
    have hright : 0 ≤ wgt * N0 / D0 := div_nonneg (mul_nonneg (le_of_lt hwgt) hN0) (le_of_lt hD0)
    linarith

theorem stageRevenue_clip_le {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k : Fin m)
    (hβ : 0 < β) (h_positiveLambda : 0 < lam k) :
    stageRevenue α β lam S p k ≤ stageRevenue α β lam S (clipPrices p) k := by
  unfold stageRevenue
  exact ratio_clip_le (lam k) (stageNumerator α β S p k)
    (stageNumerator α β S (clipPrices p) k)
    (stageDenominator α β S p k) (stageDenominator α β S (clipPrices p) k)
    h_positiveLambda (stageNumerator_clip_le α β S p k) (stageNumerator_clip_nonneg α β S p k)
    (stageDenominator_pos α β S p k) (stageDenominator_pos α β S (clipPrices p) k)
    (stageDenominator_clip_le α β S p k hβ)

theorem stageRevenue_clip_lt {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k : Fin m) (i : Fin n)
    (hi : i ∈ S k) (hneg : p i < 0) (hβ : 0 < β) (h_positiveLambda : 0 < lam k) :
    stageRevenue α β lam S p k < stageRevenue α β lam S (clipPrices p) k := by
  unfold stageRevenue
  exact ratio_clip_lt (lam k) (stageNumerator α β S p k)
    (stageNumerator α β S (clipPrices p) k)
    (stageDenominator α β S p k) (stageDenominator α β S (clipPrices p) k)
    h_positiveLambda (stageNumerator_clip_lt α β S p k i hi hneg)
    (stageNumerator_clip_nonneg α β S p k)
    (stageDenominator_pos α β S p k) (stageDenominator_pos α β S (clipPrices p) k)
    (stageDenominator_clip_le α β S p k hβ)

theorem revenue_clip_lt {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k : Fin m) (i : Fin n)
    (hi : i ∈ S k) (hneg : p i < 0) (hβ : 0 < β) (h_positiveLambda : ∀ k, 0 < lam k) :
    revenue α β lam S p < revenue α β lam S (clipPrices p) := by
  rw [revenue_eq_stageRevenue, revenue_eq_stageRevenue]
  apply Finset.sum_lt_sum
  · intro j hj
    exact stageRevenue_clip_le α β lam S p j hβ (h_positiveLambda j)
  · exact ⟨k, Finset.mem_univ k, stageRevenue_clip_lt α β lam S p k i hi hneg hβ (h_positiveLambda k)⟩

end GaoImpatientMNL.Pricing.Attempt


theorem solution {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ)
    (h : GaoImpatientMNL.Pricing.Parameters (n := n) β lam)
    (S : Fin m → Finset (Fin n)) (hS : GaoImpatientMNL.Pricing.Feasible S)
    (p : Fin n → ℝ)
    (hp : GaoImpatientMNL.Pricing.IsPricingMax α β lam S p) :
    ∀ k, ∀ i ∈ S k, 0 ≤ p i := by
  intro k i hi
  by_contra hnonneg
  have hneg : p i < 0 := lt_of_not_ge hnonneg
  rcases h with ⟨_, _, hβ, _, hLam, _⟩
  let p0 : Fin n → ℝ := GaoImpatientMNL.Pricing.Attempt.clipPrices p
  have hrev : GaoImpatientMNL.Pricing.revenue α β lam S p <
      GaoImpatientMNL.Pricing.revenue α β lam S p0 := by
    simpa [p0] using
      GaoImpatientMNL.Pricing.Attempt.revenue_clip_lt α β lam S p k i hi hneg hβ hLam
  exact (not_le_of_gt hrev) (hp p0)

#print axioms solution

