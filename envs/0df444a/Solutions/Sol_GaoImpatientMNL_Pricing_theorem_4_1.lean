-- Prove2me | solution 1 for GaoImpatientMNL.Pricing.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-29T06:04:28.966014+00:00
-- url     : https://prove2.me/submissions/d7b7e7c9-5a9a-46d4-a9a3-99ce3fd4cfa8

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

open scoped BigOperators

namespace GaoImpatientMNL.Pricing.Attempt

open GaoImpatientMNL.Pricing

/-- For nonnegative prices, each product's price-weighted attraction is bounded
by its zero-price weight divided by the common sensitivity. -/
theorem price_weight_exp_bound (a β p : ℝ) :
    β * (p * Real.exp (a - β * p)) ≤ Real.exp a := by
  have hlin : β * p ≤ Real.exp (β * p) := by
    have h := Real.add_one_le_exp (β * p)
    linarith
  calc
    β * (p * Real.exp (a - β * p)) = (β * p) * Real.exp (a - β * p) := by ring
    _ ≤ Real.exp (β * p) * Real.exp (a - β * p) :=
      mul_le_mul_of_nonneg_right hlin (le_of_lt (Real.exp_pos _))
    _ = Real.exp a := by rw [← Real.exp_add]; congr 1; ring

theorem clipped_revenue_ge {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ)
    (hβ : 0 < β) (hLam : ∀ k, 0 < lam k) :
    revenue α β lam S p ≤ revenue α β lam S (clipPrices p) := by
  rw [revenue_eq_stageRevenue, revenue_eq_stageRevenue]
  apply Finset.sum_le_sum
  intro k hk
  exact stageRevenue_clip_le α β lam S p k hβ (hLam k)

theorem clipped_numerator_bound {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k : Fin m)
    (hβ : 0 < β) :
    stageNumerator α β S (clipPrices p) k ≤
      (∑ i ∈ S k, Real.exp (α i)) / β := by
  have hsum : (∑ i ∈ S k,
      β * (clipPrices p i * Real.exp (α i - β * clipPrices p i))) ≤
      ∑ i ∈ S k, Real.exp (α i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact price_weight_exp_bound (α i) β (clipPrices p i)
  have hmul : β * stageNumerator α β S (clipPrices p) k ≤
      ∑ i ∈ S k, Real.exp (α i) := by
    rw [stageNumerator, Finset.mul_sum]
    exact hsum
  exact (le_div_iff₀ hβ).2 (by nlinarith [hmul])

theorem clipped_numerator_nonneg {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k : Fin m) :
    0 ≤ stageNumerator α β S (clipPrices p) k :=
  stageNumerator_clip_nonneg α β S p k

theorem clipped_denominator_ge_one {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k : Fin m) :
    1 ≤ stageDenominator α β S (clipPrices p) k := by
  unfold stageDenominator prefixWeight attraction
  have hW : 0 ≤ ∑ h ∈ Finset.univ.filter (fun h : Fin m => h < k),
      ∑ i ∈ S h, Real.exp (α i - β * clipPrices p i) := by
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro i hi
    exact le_of_lt (Real.exp_pos _)
  have hV : 0 ≤ ∑ i ∈ S k, Real.exp (α i - β * clipPrices p i) := by
    apply Finset.sum_nonneg
    intro i hi
    exact le_of_lt (Real.exp_pos _)
  let A := 1 + (∑ h ∈ Finset.univ.filter (fun h : Fin m => h < k),
      ∑ i ∈ S h, Real.exp (α i - β * clipPrices p i))
  let B := A + (∑ i ∈ S k, Real.exp (α i - β * clipPrices p i))
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hB : A ≤ B := by dsimp [B]; linarith
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  calc
    1 = 1 * 1 := by ring
    _ ≤ 1 * A := mul_le_mul_of_nonneg_left hA (by norm_num)
    _ ≤ A * A := mul_le_mul_of_nonneg_right hA hA0
    _ ≤ A * B := mul_le_mul_of_nonneg_left hB hA0
  

theorem clipped_stage_revenue_bound {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ)
    (k : Fin m) (hβ : 0 < β) (hLam : 0 < lam k) :
    stageRevenue α β lam S (clipPrices p) k ≤
      lam k * ((∑ i ∈ S k, Real.exp (α i)) / β) := by
  unfold stageRevenue
  have hN := clipped_numerator_bound α β S p k hβ
  have hN0 := clipped_numerator_nonneg α β S p k
  have hD1 := clipped_denominator_ge_one α β S p k
  have hD := stageDenominator_pos α β S (clipPrices p) k
  calc
    lam k * stageNumerator α β S (clipPrices p) k /
        stageDenominator α β S (clipPrices p) k ≤
      lam k * stageNumerator α β S (clipPrices p) k :=
        div_le_self (mul_nonneg (le_of_lt hLam) hN0) hD1
    _ ≤ lam k * ((∑ i ∈ S k, Real.exp (α i)) / β) :=
      mul_le_mul_of_nonneg_left hN (le_of_lt hLam)

/-- A finite, price-independent upper bound for the fixed-assortment objective.
This establishes boundedness, but not attainment: the clipped price domain is
still noncompact, and this estimate alone supplies no finite price cap. -/
theorem revenue_global_bound {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ)
    (hβ : 0 < β) (hLam : ∀ k, 0 < lam k) :
    revenue α β lam S p ≤
      ∑ k, lam k * ((∑ i ∈ S k, Real.exp (α i)) / β) := by
  calc
    revenue α β lam S p ≤ revenue α β lam S (clipPrices p) :=
      clipped_revenue_ge α β lam S p hβ hLam
    _ = ∑ k, stageRevenue α β lam S (clipPrices p) k := by
      rw [revenue_eq_stageRevenue]
    _ ≤ ∑ k, lam k * ((∑ i ∈ S k, Real.exp (α i)) / β) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa [clipPrices, max_assoc, max_left_comm, max_comm] using
        clipped_stage_revenue_bound α β lam S p k hβ (hLam k)

theorem revenue_bddAbove {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n))
    (hβ : 0 < β) (hLam : ∀ k, 0 < lam k) :
    BddAbove (Set.range (revenue α β lam S)) := by
  refine ⟨∑ k, lam k * ((∑ i ∈ S k, Real.exp (α i)) / β), ?_⟩
  rintro r ⟨p, rfl⟩
  exact revenue_global_bound α β lam S p hβ hLam

end GaoImpatientMNL.Pricing.Attempt

open scoped BigOperators
noncomputable section

namespace GaoImpatientMNL.Pricing.Attempt

open GaoImpatientMNL.Pricing

/-- Compactified discount factors. Zero corresponds to an infinite price; one
corresponds to price zero. The clamp makes the auxiliary objective defined and
continuous on all of the ambient function space. -/
def unitDiscount {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => max 0 (min 1 (x i))

def compactWeight {n : ℕ} (α : Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.exp (α i) * unitDiscount x i

def compactAttraction {n : ℕ} (α : Fin n → ℝ) (x : Fin n → ℝ)
    (s : Finset (Fin n)) : ℝ :=
  ∑ i ∈ s, compactWeight α x i

def compactPrefix {n m : ℕ} (α : Fin n → ℝ) (x : Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (k : Fin m) : ℝ :=
  prefixWeight (compactWeight α x) S k

def compactNumerator {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (x : Fin n → ℝ) (k : Fin m) : ℝ :=
  ∑ i ∈ S k, Real.exp (α i) * Real.negMulLog (unitDiscount x i) / β

def compactDenominator {n m : ℕ} (α : Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (x : Fin n → ℝ) (k : Fin m) : ℝ :=
  (1 + compactPrefix α x S k) *
    (1 + compactPrefix α x S k + compactAttraction α x (S k))

/-- Continuous extension of revenue to discounts in the closed unit interval.
At a zero discount the product's attraction and numerator are both set to zero. -/
def compactRevenue {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ)
    (S : Fin m → Finset (Fin n)) (x : Fin n → ℝ) : ℝ :=
  ∑ k, (lam k * compactNumerator α β S x k) / compactDenominator α S x k

def priceOfDiscount {n : ℕ} (β : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => -Real.log (x i) / β

theorem unitDiscount_mem {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    unitDiscount x i ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le_iff.mpr ⟨by norm_num, min_le_left _ _⟩

theorem compactWeight_nonneg {n : ℕ} (α : Fin n → ℝ) (x : Fin n → ℝ)
    (i : Fin n) : 0 ≤ compactWeight α x i :=
  mul_nonneg (le_of_lt (Real.exp_pos _)) (unitDiscount_mem x i).1

theorem compactAttraction_nonneg {n : ℕ} (α : Fin n → ℝ) (x : Fin n → ℝ)
    (s : Finset (Fin n)) : 0 ≤ compactAttraction α x s := by
  unfold compactAttraction
  apply Finset.sum_nonneg
  intro i hi
  exact compactWeight_nonneg α x i

theorem compactPrefix_nonneg {n m : ℕ} (α : Fin n → ℝ) (x : Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (k : Fin m) : 0 ≤ compactPrefix α x S k := by
  unfold compactPrefix prefixWeight
  apply Finset.sum_nonneg
  intro h hh
  apply Finset.sum_nonneg
  intro i hi
  exact compactWeight_nonneg α x i

theorem compactDenominator_pos {n m : ℕ} (α : Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (x : Fin n → ℝ) (k : Fin m) :
    0 < compactDenominator α S x k := by
  unfold compactDenominator
  have hW := compactPrefix_nonneg α x S k
  have hV := compactAttraction_nonneg α x (S k)
  positivity

theorem continuous_unitDiscount {n : ℕ} :
    Continuous (unitDiscount (n := n)) := by
  apply continuous_pi
  intro i
  simp only [unitDiscount]
  exact continuous_const.max (continuous_const.min (continuous_apply i))

theorem continuous_compactWeight {n : ℕ} (α : Fin n → ℝ) :
    Continuous (compactWeight α (n := n)) := by
  apply continuous_pi
  intro i
  simp only [compactWeight]
  exact continuous_const.mul
    (continuous_const.max (continuous_const.min (continuous_apply i)))

theorem continuous_compactNumerator {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (k : Fin m) :
    Continuous (fun x => compactNumerator α β S x k) := by
  unfold compactNumerator unitDiscount
  fun_prop

theorem continuous_compactDenominator {n m : ℕ} (α : Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (k : Fin m) :
    Continuous (fun x => compactDenominator α S x k) := by
  unfold compactDenominator compactPrefix compactAttraction compactWeight unitDiscount prefixWeight
  fun_prop

theorem continuous_compactRevenue {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n)) :
    Continuous (compactRevenue α β lam S) := by
  unfold compactRevenue
  apply continuous_finsetSum
  intro k hk
  have hnum : Continuous (fun x => lam k * compactNumerator α β S x k) :=
    continuous_const.mul (continuous_compactNumerator α β S k)
  have hden : Continuous (fun x => compactDenominator α S x k) :=
    continuous_compactDenominator α S k
  exact hnum.div hden (fun x => (compactDenominator_pos α S x k).ne')

theorem compact_discount_box_nonempty {n : ℕ} :
    (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1).Nonempty := by
  refine ⟨fun _ => 1, ?_⟩
  intro i hi
  simp

theorem compact_discount_box_isCompact {n : ℕ} :
    IsCompact (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
  apply isCompact_univ_pi
  intro i
  exact isCompact_Icc

/-- The compactified objective has an attained maximum on the closed discount
box. The separate boundary-exclusion step is still needed to obtain finite prices. -/
theorem compactified_maximum_exists {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n)) :
    ∃ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
      IsMaxOn (compactRevenue α β lam S)
        (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) x := by
  exact compact_discount_box_isCompact.exists_isMaxOn
    compact_discount_box_nonempty (continuous_compactRevenue α β lam S).continuousOn

theorem unitDiscount_eq_self_of_mem {n : ℕ} (x : Fin n → ℝ) (i : Fin n)
    (hx : x i ∈ Set.Icc (0 : ℝ) 1) : unitDiscount x i = x i := by
  simp [unitDiscount, max_eq_right hx.1, min_eq_right hx.2]

theorem compactRevenue_eq_revenue_of_positive {n m : ℕ} (α : Fin n → ℝ)
    (β : ℝ) (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n)) (x : Fin n → ℝ)
    (hβ : 0 < β) (hxbox : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
    (hxpos : ∀ k i, i ∈ S k → 0 < x i) :
    compactRevenue α β lam S x =
      revenue α β lam S (priceOfDiscount β x) := by
  have hweight (k : Fin m) (i : Fin n) (hi : i ∈ S k) :
      compactWeight α x i = Real.exp (α i - β * priceOfDiscount β x i) := by
    have hxi : x i ∈ Set.Icc (0 : ℝ) 1 := hxbox i (Set.mem_univ i)
    have hu := unitDiscount_eq_self_of_mem x i hxi
    have hxip := hxpos k i hi
    have harg : α i - β * priceOfDiscount β x i = α i + Real.log (x i) := by
      dsimp [priceOfDiscount]
      field_simp
      ring
    rw [show compactWeight α x i = Real.exp (α i) * x i by
      simp [compactWeight, hu]]
    rw [harg, Real.exp_add, Real.exp_log hxip]
  have hatt (k : Fin m) :
      compactAttraction α x (S k) = attraction α β (priceOfDiscount β x) (S k) := by
    unfold compactAttraction attraction
    apply Finset.sum_congr rfl
    intro i hi
    exact hweight k i hi
  have hprefix (k : Fin m) :
      compactPrefix α x S k =
        prefixWeight (fun i => Real.exp (α i - β * priceOfDiscount β x i)) S k := by
    unfold compactPrefix prefixWeight
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro i hi
    exact hweight h i hi
  have hnum (k : Fin m) : compactNumerator α β S x k =
      stageNumerator α β S (priceOfDiscount β x) k := by
    unfold compactNumerator stageNumerator
    apply Finset.sum_congr rfl
    intro i hi
    have hxi : x i ∈ Set.Icc (0 : ℝ) 1 := hxbox i (Set.mem_univ i)
    have hu := unitDiscount_eq_self_of_mem x i hxi
    have hxip := hxpos k i hi
    have harg : α i - β * priceOfDiscount β x i = α i + Real.log (x i) := by
      dsimp [priceOfDiscount]
      field_simp
      ring
    rw [hu, harg, Real.exp_add, Real.exp_log hxip]
    dsimp [priceOfDiscount]
    rw [Real.negMulLog]
    field_simp [hβ.ne']
    <;> ring_nf
  have hden (k : Fin m) : compactDenominator α S x k =
      stageDenominator α β S (priceOfDiscount β x) k := by
    simp [compactDenominator, stageDenominator, hprefix k, hatt k]
  unfold compactRevenue revenue
  apply Finset.sum_congr rfl
  intro k hk
  rw [hnum k, hden k]
  simp only [stageNumerator, stageDenominator]

theorem compactified_maximum_gives_pricing_max {n m : ℕ} (α : Fin n → ℝ)
    (β : ℝ) (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n))
    (hβ : 0 < β) (hLam : ∀ k, 0 < lam k)
    (x : Fin n → ℝ)
    (hxbox : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
    (hmax : IsMaxOn (compactRevenue α β lam S)
      (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) x)
    (hxpos : ∀ k i, i ∈ S k → 0 < x i) :
    IsPricingMax α β lam S (priceOfDiscount β x) := by
  intro p'
  let clipped := clipPrices p'
  let y : Fin n → ℝ := fun i => Real.exp (-β * clipped i)
  have hybox : y ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
    intro i hi
    constructor
    · exact le_of_lt (Real.exp_pos _)
    · apply Real.exp_le_one_iff.mpr
      have hp : 0 ≤ clipped i := le_max_left 0 (p' i)
      nlinarith
  have hypos (k : Fin m) (i : Fin n) (hi : i ∈ S k) : 0 < y i :=
    Real.exp_pos _
  have hprice : priceOfDiscount β y = clipped := by
    funext i
    simp [priceOfDiscount, y, Real.log_exp]
    field_simp [hβ.ne']
    <;> ring
  have hcompact_y : compactRevenue α β lam S y = revenue α β lam S clipped := by
    rw [compactRevenue_eq_revenue_of_positive α β lam S y hβ hybox hypos, hprice]
  have hcompact_x : compactRevenue α β lam S x =
      revenue α β lam S (priceOfDiscount β x) :=
    compactRevenue_eq_revenue_of_positive α β lam S x hβ hxbox hxpos
  calc
    revenue α β lam S p' ≤ revenue α β lam S clipped :=
      clipped_revenue_ge α β lam S p' hβ hLam
    _ = compactRevenue α β lam S y := hcompact_y.symm
    _ ≤ compactRevenue α β lam S x := hmax hybox
    _ = revenue α β lam S (priceOfDiscount β x) := hcompact_x

end GaoImpatientMNL.Pricing.Attempt

end

open scoped BigOperators

namespace GaoImpatientMNL.Pricing.Attempt

open GaoImpatientMNL.Pricing

noncomputable def commonPrice {n : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (p : Fin n → ℝ) (s : Finset (Fin n)) : ℝ :=
  Real.log ((∑ i ∈ s, Real.exp (α i)) /
    (∑ i ∈ s, Real.exp (α i - β * p i))) / β

noncomputable def replaceStagePrices {n : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (p : Fin n → ℝ) (s : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ s then commonPrice α β p s else p i

/-- The revenue numerator at unequal nonnegative prices is no larger than the
numerator obtained by replacing them with the common price that preserves total
attraction. This is the weighted log-sum-exp (Jensen) inequality. -/
theorem stageNumerator_le_commonPrice {n : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (p : Fin n → ℝ) (s : Finset (Fin n)) (hs : s.Nonempty)
    (hβ : 0 < β) :
    (∑ i ∈ s, p i * Real.exp (α i - β * p i)) ≤
      (Real.log ((∑ i ∈ s, Real.exp (α i)) /
        (∑ i ∈ s, Real.exp (α i - β * p i))) / β) *
        (∑ i ∈ s, Real.exp (α i - β * p i)) := by
  let V : ℝ := ∑ i ∈ s, Real.exp (α i - β * p i)
  let C : ℝ := ∑ i ∈ s, Real.exp (α i)
  let w : Fin n → ℝ := fun i => Real.exp (α i - β * p i) / V
  have hV : 0 < V := by
    dsimp [V]
    exact Finset.sum_pos (fun i hi => Real.exp_pos _) hs
  have hC : 0 < C := by
    dsimp [C]
    exact Finset.sum_pos (fun i hi => Real.exp_pos _) hs
  have hw_nonneg : ∀ i ∈ s, 0 ≤ w i := by
    intro i hi
    exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt hV)
  have hw_sum : (∑ i ∈ s, w i) = 1 := by
    calc
      (∑ i ∈ s, w i) = V / V := by simp [w, V, Finset.sum_div]
      _ = 1 := div_self hV.ne'
  have hw_exp : (∑ i ∈ s, w i * Real.exp (β * p i)) = C / V := by
    calc
      (∑ i ∈ s, w i * Real.exp (β * p i)) =
          ∑ i ∈ s, Real.exp (α i) / V := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [w]
        rw [div_mul_eq_mul_div]
        rw [← Real.exp_add]
        congr 1
        ring_nf
      _ = C / V := by simp [C, Finset.sum_div]
  have hJensen : Real.exp (∑ i ∈ s, w i * (β * p i)) ≤ C / V := by
    have h := convexOn_exp.map_sum_le (t := s) (w := w)
      (p := fun i => β * p i) hw_nonneg hw_sum (by intro i hi; exact Set.mem_univ _)
    simpa only [smul_eq_mul] using h.trans_eq hw_exp
  have hlog : (∑ i ∈ s, w i * (β * p i)) ≤ Real.log (C / V) := by
    have hratio : 0 < C / V := div_pos hC hV
    apply Real.exp_le_exp.mp
    calc
      Real.exp (∑ i ∈ s, w i * (β * p i)) ≤ C / V := hJensen
      _ = Real.exp (Real.log (C / V)) := (Real.exp_log hratio).symm
  have hweighted : (∑ i ∈ s, w i * (β * p i)) =
      (β / V) * (∑ i ∈ s, p i * Real.exp (α i - β * p i)) := by
    unfold w
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [hV.ne']
  have hscale := mul_le_mul_of_nonneg_left hlog (le_of_lt (div_pos hV hβ))
  rw [hweighted] at hscale
  have hcoeff : (V / β) * (β / V) = 1 := by
    field_simp [hV.ne', hβ.ne']
  have hN : (∑ i ∈ s, p i * Real.exp (α i - β * p i)) ≤
      (V / β) * Real.log (C / V) := by
    calc
      (∑ i ∈ s, p i * Real.exp (α i - β * p i)) =
          (V / β) * ((β / V) *
            (∑ i ∈ s, p i * Real.exp (α i - β * p i))) := by
              rw [← mul_assoc, hcoeff]
              simp
      _ ≤ (V / β) * Real.log (C / V) := hscale
  calc
    (∑ i ∈ s, p i * Real.exp (α i - β * p i)) ≤
        (V / β) * Real.log (C / V) := hN
    _ = (Real.log (C / V) / β) * V := by ring

/-- Replacing prices on a stage by the common price that preserves its total
attraction leaves that attraction unchanged. -/
theorem attraction_commonPrice_replacement {n : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (p : Fin n → ℝ) (s : Finset (Fin n)) (hs : s.Nonempty) (hβ : 0 < β) :
    attraction α β (fun i => if i ∈ s then
      Real.log ((∑ j ∈ s, Real.exp (α j)) /
        (∑ j ∈ s, Real.exp (α j - β * p j))) / β else p i) s =
      attraction α β p s := by
  let V : ℝ := ∑ i ∈ s, Real.exp (α i - β * p i)
  let C : ℝ := ∑ i ∈ s, Real.exp (α i)
  let q : ℝ := Real.log (C / V) / β
  have hV : 0 < V := by
    dsimp [V]
    exact Finset.sum_pos (fun i hi => Real.exp_pos _) hs
  have hC : 0 < C := by
    dsimp [C]
    exact Finset.sum_pos (fun i hi => Real.exp_pos _) hs
  have hratio : 0 < C / V := div_pos hC hV
  have hscale : Real.exp (-β * q) = V / C := by
    dsimp [q]
    rw [show -β * (Real.log (C / V) / β) = -Real.log (C / V) by
      field_simp]
    rw [Real.exp_neg, Real.exp_log hratio]
    field_simp
  have hterm (i : Fin n) :
      Real.exp (α i - β * q) = Real.exp (α i) * (V / C) := by
    rw [show α i - β * q = α i + (-β * q) by ring, Real.exp_add, hscale]
  have hsum : (∑ i ∈ s, Real.exp (α i - β * q)) = V := by
    calc
      (∑ i ∈ s, Real.exp (α i - β * q)) = C * (V / C) := by
        rw [show (∑ i ∈ s, Real.exp (α i - β * q)) =
          ∑ i ∈ s, Real.exp (α i) * (V / C) by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i]
        rw [← Finset.sum_mul]
      _ = V := by field_simp
  unfold attraction
  calc
    (∑ i ∈ s, Real.exp (α i - β * (if i ∈ s then q else p i))) =
        ∑ i ∈ s, Real.exp (α i - β * q) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [hi]
    _ = V := hsum
    _ = (∑ i ∈ s, Real.exp (α i - β * p i)) := rfl

/-- On the replaced stage, the new numerator is the common price times the
preserved total attraction. -/
theorem stageNumerator_commonPrice_replacement {n : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (p : Fin n → ℝ) (s : Finset (Fin n)) (hs : s.Nonempty) (hβ : 0 < β) :
    (∑ i ∈ s, (if i ∈ s then
      Real.log ((∑ j ∈ s, Real.exp (α j)) /
        (∑ j ∈ s, Real.exp (α j - β * p j))) / β else p i) *
        Real.exp (α i - β * (if i ∈ s then
          Real.log ((∑ j ∈ s, Real.exp (α j)) /
            (∑ j ∈ s, Real.exp (α j - β * p j))) / β else p i))) =
      (Real.log ((∑ j ∈ s, Real.exp (α j)) /
        (∑ j ∈ s, Real.exp (α j - β * p j))) / β) *
        (∑ i ∈ s, Real.exp (α i - β * p i)) := by
  let q : ℝ := Real.log ((∑ j ∈ s, Real.exp (α j)) /
      (∑ j ∈ s, Real.exp (α j - β * p j))) / β
  have hsum : (∑ i ∈ s, Real.exp (α i - β * q)) =
      ∑ i ∈ s, Real.exp (α i - β * p i) := by
    calc
      (∑ i ∈ s, Real.exp (α i - β * q)) =
          attraction α β (fun i => if i ∈ s then q else p i) s := by
            unfold attraction
            apply Finset.sum_congr rfl
            intro i hi
            simp [hi]
      _ = attraction α β p s := attraction_commonPrice_replacement α β p s hs hβ
      _ = ∑ i ∈ s, Real.exp (α i - β * p i) := rfl
  calc
    (∑ i ∈ s, (if i ∈ s then q else p i) *
        Real.exp (α i - β * (if i ∈ s then q else p i))) =
        ∑ i ∈ s, q * Real.exp (α i - β * q) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [hi]
    _ = q * (∑ i ∈ s, Real.exp (α i - β * q)) := by rw [Finset.mul_sum]
    _ = q * (∑ i ∈ s, Real.exp (α i - β * p i)) := by rw [hsum]

theorem attraction_replaceStagePrices {n : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (p : Fin n → ℝ) (s : Finset (Fin n)) (hs : s.Nonempty) (hβ : 0 < β) :
    attraction α β (replaceStagePrices α β p s) s = attraction α β p s := by
  change attraction α β (fun i => if i ∈ s then
    Real.log ((∑ j ∈ s, Real.exp (α j)) /
      (∑ j ∈ s, Real.exp (α j - β * p j))) / β else p i) s = _
  exact attraction_commonPrice_replacement α β p s hs hβ

theorem attraction_replaceStagePrices_disjoint {n : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (p : Fin n → ℝ) (s t : Finset (Fin n)) (hst : Disjoint s t) :
    attraction α β (replaceStagePrices α β p s) t = attraction α β p t := by
  unfold attraction
  apply Finset.sum_congr rfl
  intro i hi
  have his : i ∉ s := by
    intro his
    exact (Finset.disjoint_left.mp hst.symm) hi his
  simp [replaceStagePrices, his]

theorem attraction_replaceStagePrices_all {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (p : Fin n → ℝ) (S : Fin m → Finset (Fin n)) (k h : Fin m)
    (hS : Feasible S) (hβ : 0 < β) (hSk : (S k).Nonempty) :
    attraction α β (replaceStagePrices α β p (S k)) (S h) =
      attraction α β p (S h) := by
  by_cases hkh : k = h
  · subst h
    exact attraction_replaceStagePrices α β p (S k) hSk hβ
  · apply attraction_replaceStagePrices_disjoint
    exact hS k h hkh

theorem prefixWeight_replaceStagePrices {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (p : Fin n → ℝ) (S : Fin m → Finset (Fin n)) (k h : Fin m)
    (hS : Feasible S) (hβ : 0 < β) (hSk : (S k).Nonempty) :
    prefixWeight (fun i => Real.exp (α i - β * replaceStagePrices α β p (S k) i)) S h =
      prefixWeight (fun i => Real.exp (α i - β * p i)) S h := by
  unfold prefixWeight
  apply Finset.sum_congr rfl
  intro t ht
  exact attraction_replaceStagePrices_all α β p S k t hS hβ hSk

theorem stageNumerator_replaceStagePrices_ge {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (p : Fin n → ℝ) (S : Fin m → Finset (Fin n)) (k h : Fin m)
    (hS : Feasible S) (hβ : 0 < β) (hSk : (S k).Nonempty) :
    stageNumerator α β S p h ≤
      stageNumerator α β S (replaceStagePrices α β p (S k)) h := by
  by_cases hkh : k = h
  · subst h
    let q := commonPrice α β p (S k)
    have hle := stageNumerator_le_commonPrice α β p (S k) hSk hβ
    have hnew : stageNumerator α β S (replaceStagePrices α β p (S k)) k =
        q * attraction α β p (S k) := by
      simpa [stageNumerator, attraction, replaceStagePrices, commonPrice, q] using
        stageNumerator_commonPrice_replacement α β p (S k) hSk hβ
    change stageNumerator α β S p k ≤
      stageNumerator α β S (replaceStagePrices α β p (S k)) k
    calc
      stageNumerator α β S p k ≤ q * attraction α β p (S k) := by
        simpa [stageNumerator, attraction, commonPrice, q] using hle
      _ = stageNumerator α β S (replaceStagePrices α β p (S k)) k := hnew.symm
  · unfold stageNumerator
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro i hi
    have his : i ∉ S k := by
      intro his
      exact (Finset.disjoint_left.mp (hS k h hkh).symm) hi his
    simp [replaceStagePrices, his]

theorem stageNumerator_replaceStagePrices_eq_of_ne {n m : ℕ} (α : Fin n → ℝ)
    (β : ℝ) (p : Fin n → ℝ) (S : Fin m → Finset (Fin n)) (k h : Fin m)
    (hS : Feasible S) (hkh : k ≠ h) :
    stageNumerator α β S (replaceStagePrices α β p (S k)) h =
      stageNumerator α β S p h := by
  unfold stageNumerator
  apply Finset.sum_congr rfl
  intro i hi
  have his : i ∉ S k := by
    intro his
    exact (Finset.disjoint_left.mp (hS k h hkh).symm) hi his
  simp [replaceStagePrices, his]

theorem stageDenominator_replaceStagePrices_eq {n m : ℕ} (α : Fin n → ℝ)
    (β : ℝ) (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) (k h : Fin m)
    (hS : Feasible S) (hβ : 0 < β) (hSk : (S k).Nonempty) :
    stageDenominator α β S (replaceStagePrices α β p (S k)) h =
      stageDenominator α β S p h := by
  unfold stageDenominator
  rw [prefixWeight_replaceStagePrices α β p S k h hS hβ hSk,
    attraction_replaceStagePrices_all α β p S k h hS hβ hSk]

theorem stageRevenue_replaceStagePrices_ge {n m : ℕ} (α : Fin n → ℝ)
    (β : ℝ) (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ)
    (k : Fin m) (hS : Feasible S) (hβ : 0 < β) (hlam : 0 < lam k)
    (hSk : (S k).Nonempty) :
    stageRevenue α β lam S p k ≤
      stageRevenue α β lam S (replaceStagePrices α β p (S k)) k := by
  unfold stageRevenue
  rw [stageDenominator_replaceStagePrices_eq α β S p k k hS hβ hSk]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (stageNumerator_replaceStagePrices_ge α β p S k k hS hβ hSk)
      (le_of_lt hlam))
    (le_of_lt (stageDenominator_pos α β S p k))

theorem stageRevenue_replaceStagePrices_eq_of_ne {n m : ℕ} (α : Fin n → ℝ)
    (β : ℝ) (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ)
    (k h : Fin m) (hS : Feasible S) (hkh : k ≠ h) (hβ : 0 < β)
    (hSk : (S k).Nonempty) :
    stageRevenue α β lam S (replaceStagePrices α β p (S k)) h =
      stageRevenue α β lam S p h := by
  unfold stageRevenue
  rw [stageNumerator_replaceStagePrices_eq_of_ne α β p S k h hS hkh,
    stageDenominator_replaceStagePrices_eq α β S p k h hS hβ hSk]

theorem revenue_replaceStagePrices_ge {n m : ℕ} (α : Fin n → ℝ)
    (β : ℝ) (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ)
    (k : Fin m) (hS : Feasible S) (hβ : 0 < β)
    (hLam : ∀ h, 0 < lam h) (hSk : (S k).Nonempty) :
    revenue α β lam S p ≤
      revenue α β lam S (replaceStagePrices α β p (S k)) := by
  rw [revenue_eq_stageRevenue, revenue_eq_stageRevenue]
  apply Finset.sum_le_sum
  intro h hh
  by_cases hkh : k = h
  · subst h
    exact stageRevenue_replaceStagePrices_ge α β lam S p k hS hβ (hLam k) hSk
  · exact (stageRevenue_replaceStagePrices_eq_of_ne α β lam S p k h hS hkh hβ hSk).symm.le


theorem exists_equalized_on_stages {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n)) (hS : Feasible S)
    (hβ : 0 < β) (hLam : ∀ h, 0 < lam h) (p : Fin n → ℝ) :
    ∀ t : Finset (Fin m), ∃ q : Fin n → ℝ,
      revenue α β lam S p ≤ revenue α β lam S q ∧
      ∀ h ∈ t, ∀ i ∈ S h, ∀ j ∈ S h, q i = q j := by
  intro t
  induction t using Finset.induction_on with
  | empty =>
      exact ⟨p, le_rfl, by simp⟩
  | @insert k t hkt ih =>
      obtain ⟨q, hpq, hqt⟩ := ih
      by_cases hSk : (S k).Nonempty
      · let q' := replaceStagePrices α β q (S k)
        have hrev := revenue_replaceStagePrices_ge α β lam S q k hS hβ hLam hSk
        refine ⟨q', hpq.trans ?_, ?_⟩
        · simpa [q'] using hrev
        · intro h hh i hi j hj
          simp only [Finset.mem_insert] at hh
          rcases hh with rfl | hht
          · simp [q', replaceStagePrices, hi, hj]
          · have hhk : h ≠ k := by
              intro heq
              subst h
              exact hkt hht
            have hkh : k ≠ h := Ne.symm hhk
            have hi_out : i ∉ S k := by
              intro hik
              exact (Finset.disjoint_left.mp (hS k h hkh).symm) hi hik
            have hj_out : j ∉ S k := by
              intro hjk
              exact (Finset.disjoint_left.mp (hS k h hkh).symm) hj hjk
            simpa [q', replaceStagePrices, hi_out, hj_out] using hqt h hht i hi j hj
      · refine ⟨q, hpq, ?_⟩
        intro h hh i hi j hj
        simp only [Finset.mem_insert] at hh
        rcases hh with rfl | hht
        · exact (hSk ⟨i, hi⟩).elim
        · exact hqt h hht i hi j hj

theorem equalized_maximizer_of_maximizer {n m : ℕ} (α : Fin n → ℝ)
    (β : ℝ) (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n))
    (hS : Feasible S) (hβ : 0 < β) (hLam : ∀ h, 0 < lam h)
    (p : Fin n → ℝ) (hp : IsPricingMax α β lam S p) :
    ∃ q : Fin n → ℝ, IsPricingMax α β lam S q ∧
      ∀ k, ∀ i ∈ S k, ∀ j ∈ S k, q i = q j := by
  obtain ⟨q, hpq, hqe⟩ :=
    exists_equalized_on_stages α β lam S hS hβ hLam p Finset.univ
  have hrev : revenue α β lam S p = revenue α β lam S q :=
    le_antisymm hpq (hp q)
  refine ⟨q, ?_, ?_⟩
  · intro p'
    calc
      revenue α β lam S p' ≤ revenue α β lam S p := hp p'
      _ = revenue α β lam S q := hrev
  · intro k i hi j hj
    exact hqe k (Finset.mem_univ k) i hi j hj

end GaoImpatientMNL.Pricing.Attempt

open scoped BigOperators

namespace GaoImpatientMNL.Pricing.Attempt

open GaoImpatientMNL.Pricing

def updateDiscount {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (z : ℝ) : Fin n → ℝ :=
  Function.update x i z

theorem updateDiscount_mem_box {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (z : ℝ)
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    updateDiscount x i z ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
  intro j hj
  by_cases hji : j = i
  · subst j
    simpa [updateDiscount] using hz
  · have hxj := hx j (Set.mem_univ j)
    simpa [updateDiscount, Function.update_of_ne hji] using hxj

theorem compactWeight_update {n : ℕ} (α : Fin n → ℝ) (x : Fin n → ℝ)
    (i j : Fin n) (z : ℝ)
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
    (hxi : x i = 0) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    compactWeight α (updateDiscount x i z) j =
      compactWeight α x j + if j = i then Real.exp (α i) * z else 0 := by
  have hy := updateDiscount_mem_box x i z hx hz
  change Real.exp (α j) * unitDiscount (updateDiscount x i z) j =
    Real.exp (α j) * unitDiscount x j + if j = i then Real.exp (α i) * z else 0
  rw [unitDiscount_eq_self_of_mem (updateDiscount x i z) j (hy j (Set.mem_univ j)),
    unitDiscount_eq_self_of_mem x j (hx j (Set.mem_univ j))]
  by_cases hji : j = i
  · subst j
    simp [updateDiscount, Function.update_self, hxi]
  · rw [updateDiscount, Function.update_of_ne hji]
    simp [hji]

theorem compactAttraction_update {n : ℕ} (α : Fin n → ℝ) (x : Fin n → ℝ)
    (i : Fin n) (z : ℝ) (s : Finset (Fin n))
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
    (hxi : x i = 0) (hz : z ∈ Set.Icc (0 : ℝ) 1) (hi : i ∈ s) :
    compactAttraction α (updateDiscount x i z) s =
      compactAttraction α x s + Real.exp (α i) * z := by
  unfold compactAttraction
  calc
    (∑ j ∈ s, compactWeight α (updateDiscount x i z) j) =
        ∑ j ∈ s, (compactWeight α x j +
          if j = i then Real.exp (α i) * z else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact compactWeight_update α x i j z hx hxi hz
    _ = (∑ j ∈ s, compactWeight α x j) + Real.exp (α i) * z := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp [hi]

theorem compactAttraction_update_of_not_mem {n : ℕ} (α : Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) (z : ℝ) (s : Finset (Fin n))
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
    (hxi : x i = 0) (hz : z ∈ Set.Icc (0 : ℝ) 1) (hi : i ∉ s) :
    compactAttraction α (updateDiscount x i z) s = compactAttraction α x s := by
  unfold compactAttraction
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hi hj
  rw [compactWeight_update α x i j z hx hxi hz]
  simp [hji]

theorem compactPrefix_update {n m : ℕ} (α : Fin n → ℝ) (x : Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (i : Fin n) (z : ℝ) (k h : Fin m)
    (hS : Feasible S)
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
    (hxi : x i = 0) (hz : z ∈ Set.Icc (0 : ℝ) 1) (hi : i ∈ S k) :
    compactPrefix α (updateDiscount x i z) S h =
      compactPrefix α x S h + if k < h then Real.exp (α i) * z else 0 := by
  unfold compactPrefix prefixWeight
  calc
    (∑ t ∈ Finset.univ.filter (fun t : Fin m => t < h),
        ∑ j ∈ S t, compactWeight α (updateDiscount x i z) j) =
      ∑ t ∈ Finset.univ.filter (fun t : Fin m => t < h),
        ((∑ j ∈ S t, compactWeight α x j) +
          if t = k then Real.exp (α i) * z else 0) := by
        apply Finset.sum_congr rfl
        intro t ht
        change compactAttraction α (updateDiscount x i z) (S t) =
          compactAttraction α x (S t) + if t = k then Real.exp (α i) * z else 0
        by_cases htk : t = k
        · subst t
          rw [compactAttraction_update α x i z (S k) hx hxi hz hi]
          simp
        · have hIt : i ∉ S t := by
            intro hit
            exact (Finset.disjoint_left.mp (hS k t (Ne.symm htk))) hi hit
          rw [compactAttraction_update_of_not_mem α x i z (S t) hx hxi hz hIt]
          simp [htk]
    _ = (∑ t ∈ Finset.univ.filter (fun t : Fin m => t < h),
          ∑ j ∈ S t, compactWeight α x j) +
        if k < h then Real.exp (α i) * z else 0 := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp [Finset.mem_filter]

theorem compactNumerator_update {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (x : Fin n → ℝ) (i : Fin n) (z : ℝ)
    (k : Fin m) (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
    (hxi : x i = 0) (hz : z ∈ Set.Icc (0 : ℝ) 1) (hi : i ∈ S k) :
    compactNumerator α β S (updateDiscount x i z) k =
      compactNumerator α β S x k + Real.exp (α i) * Real.negMulLog z / β := by
  have hy := updateDiscount_mem_box x i z hx hz
  unfold compactNumerator
  calc
    (∑ j ∈ S k, Real.exp (α j) * Real.negMulLog
        (unitDiscount (updateDiscount x i z) j) / β) =
      ∑ j ∈ S k, (Real.exp (α j) * Real.negMulLog (unitDiscount x j) / β +
        if j = i then Real.exp (α i) * Real.negMulLog z / β else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [unitDiscount_eq_self_of_mem (updateDiscount x i z) j (hy j (Set.mem_univ j)),
          unitDiscount_eq_self_of_mem x j (hx j (Set.mem_univ j))]
        by_cases hji : j = i
        · subst j
          simp [updateDiscount, Function.update_self, hxi]
        · rw [updateDiscount, Function.update_of_ne hji]
          simp [hji]
    _ = (∑ j ∈ S k, Real.exp (α j) * Real.negMulLog (unitDiscount x j) / β) +
        Real.exp (α i) * Real.negMulLog z / β := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp [hi]

theorem compactNumerator_update_of_not_mem {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (x : Fin n → ℝ) (i : Fin n) (z : ℝ)
    (k : Fin m) (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
    (hxi : x i = 0) (hz : z ∈ Set.Icc (0 : ℝ) 1) (hi : i ∉ S k) :
    compactNumerator α β S (updateDiscount x i z) k = compactNumerator α β S x k := by
  have hy := updateDiscount_mem_box x i z hx hz
  unfold compactNumerator
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hi hj
  rw [unitDiscount_eq_self_of_mem (updateDiscount x i z) j (hy j (Set.mem_univ j)),
    unitDiscount_eq_self_of_mem x j (hx j (Set.mem_univ j)), updateDiscount,
    Function.update_of_ne hji]

theorem negMulLog_exp_price (β T : ℝ) (hβ : β ≠ 0) :
    Real.negMulLog (Real.exp (-β * T)) / β = Real.exp (-β * T) * T := by
  rw [Real.negMulLog, Real.log_exp]
  field_simp [hβ]
  <;> ring_nf

theorem compactDenominator_update_target {n m : ℕ} (α : Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (x : Fin n → ℝ) (i : Fin n) (z : ℝ)
    (k : Fin m) (hS : Feasible S)
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
    (hxi : x i = 0) (hz : z ∈ Set.Icc (0 : ℝ) 1) (hi : i ∈ S k) :
    compactDenominator α S (updateDiscount x i z) k =
      (1 + compactPrefix α x S k) *
        (1 + compactPrefix α x S k + compactAttraction α x (S k) +
          Real.exp (α i) * z) := by
  have hp := compactPrefix_update α x S i z k k hS hx hxi hz hi
  have hp' : compactPrefix α (updateDiscount x i z) S k =
      compactPrefix α x S k := by simpa using hp
  have hv := compactAttraction_update α x i z (S k) hx hxi hz hi
  unfold compactDenominator
  rw [hp', hv]
  ring

theorem compactDenominator_update_future {n m : ℕ} (α : Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (x : Fin n → ℝ) (i : Fin n) (z : ℝ)
    (k h : Fin m) (hkh : k < h) (hS : Feasible S)
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
    (hxi : x i = 0) (hz : z ∈ Set.Icc (0 : ℝ) 1) (hi : i ∈ S k) :
    compactDenominator α S (updateDiscount x i z) h =
      (1 + compactPrefix α x S h + Real.exp (α i) * z) *
        (1 + compactPrefix α x S h + compactAttraction α x (S h) +
          Real.exp (α i) * z) := by
  have hp := compactPrefix_update α x S i z k h hS hx hxi hz hi
  have hp' : compactPrefix α (updateDiscount x i z) S h =
      compactPrefix α x S h + Real.exp (α i) * z := by
    simpa [hkh] using hp
  have hnot : i ∉ S h := by
    intro hit
    exact (Finset.disjoint_left.mp (hS k h (ne_of_lt hkh))) hi hit
  have hv := compactAttraction_update_of_not_mem α x i z (S h) hx hxi hz hnot
  unfold compactDenominator
  rw [hp', hv]
  ring

theorem compactDenominator_update_past {n m : ℕ} (α : Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (x : Fin n → ℝ) (i : Fin n) (z : ℝ)
    (k h : Fin m) (hkh : h < k) (hS : Feasible S)
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
    (hxi : x i = 0) (hz : z ∈ Set.Icc (0 : ℝ) 1) (hi : i ∈ S k) :
    compactDenominator α S (updateDiscount x i z) h = compactDenominator α S x h := by
  have hp := compactPrefix_update α x S i z k h hS hx hxi hz hi
  have hp' : compactPrefix α (updateDiscount x i z) S h = compactPrefix α x S h := by
    simpa [not_lt_of_ge (le_of_lt hkh)] using hp
  have hnot : i ∉ S h := by
    intro hit
    exact (Finset.disjoint_left.mp (hS k h (ne_of_gt hkh))) hi hit
  have hv := compactAttraction_update_of_not_mem α x i z (S h) hx hxi hz hnot
  simp [compactDenominator, hp', hv]

noncomputable def compactStageRevenue {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n)) (x : Fin n → ℝ)
    (k : Fin m) : ℝ :=
  lam k * compactNumerator α β S x k / compactDenominator α S x k

theorem compactRevenue_eq_compactStageRevenue {n m : ℕ} (α : Fin n → ℝ)
    (β : ℝ) (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n)) (x : Fin n → ℝ) :
    compactRevenue α β lam S x = ∑ k, compactStageRevenue α β lam S x k := rfl

theorem compactNumerator_nonneg {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (x : Fin n → ℝ) (k : Fin m) (hβ : 0 < β) :
    0 ≤ compactNumerator α β S x k := by
  unfold compactNumerator
  apply Finset.sum_nonneg
  intro i hi
  apply div_nonneg
  · apply mul_nonneg (le_of_lt (Real.exp_pos _))
    exact Real.negMulLog_nonneg (unitDiscount_mem x i).1 (unitDiscount_mem x i).2
  · exact le_of_lt hβ

theorem boundary_gain_beats_linear_loss
    (A B N lam a β C : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hN : 0 ≤ N)
    (hlam : 0 < lam) (ha : 0 < a) (hβ : 0 < β) (hC : 0 ≤ C) :
    ∃ T z : ℝ, z = Real.exp (-β * T) ∧ 0 < z ∧ z ≤ 1 ∧
      lam * (N + a * (z * T)) / (A * (B + a * z)) -
          lam * N / (A * B) > C * z := by
  let T := N / B + (C + 1) * A * (B + a) / (lam * a)
  let z := Real.exp (-β * T)
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hz : 0 < z := Real.exp_pos _
  have hzle : z ≤ 1 := by
    dsimp [z]
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hscale :
      (lam * (N + a * (z * T)) / (A * (B + a * z)) -
        lam * N / (A * B)) =
      z * (C + 1) * (B + a) / (B + a * z) := by
    dsimp [T]
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hlam,
      ne_of_gt ha, ne_of_gt hβ]
    <;> ring
  refine ⟨T, z, rfl, hz, hzle, ?_⟩
  rw [hscale]
  have hden : 0 < B + a * z := by positivity
  have hratio : 1 ≤ (B + a) / (B + a * z) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hfactor : 0 ≤ z * (C + 1) :=
    mul_nonneg (le_of_lt hz) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hratio hfactor
  have hstrict : C * z < z * (C + 1) := by nlinarith
  calc
    C * z < z * (C + 1) := hstrict
    _ ≤ z * (C + 1) * ((B + a) / (B + a * z)) := by
      simpa [mul_assoc] using hmul
    _ = z * (C + 1) * (B + a) / (B + a * z) := by ring

theorem future_loss_le_linear
    (A B N lam a z : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hN : 0 ≤ N)
    (hlam : 0 ≤ lam) (ha : 0 ≤ a) (hz : 0 ≤ z) (hzle : z ≤ 1) :
    lam * N / (A * B) - lam * N / ((A + a * z) * (B + a * z)) ≤
      z * (lam * N * (a * (A + B) + a ^ 2) / (A ^ 2 * B ^ 2)) := by
  have hAz : 0 < A + a * z := by positivity
  have hBz : 0 < B + a * z := by positivity
  have hD : 0 < A * B * (A + a * z) * (B + a * z) := by positivity
  have hD0 : 0 < A ^ 2 * B ^ 2 := by positivity
  have hnum :
      lam * N / (A * B) - lam * N / ((A + a * z) * (B + a * z)) =
        (lam * N * (z * (a * (A + B) + a ^ 2 * z))) /
          (A * B * (A + a * z) * (B + a * z)) := by
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hAz, ne_of_gt hBz]
    <;> ring
  have hcore : z * (a * (A + B) + a ^ 2 * z) ≤
      z * (a * (A + B) + a ^ 2) := by
    have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
    have hinner : a * (A + B) + a ^ 2 * z ≤ a * (A + B) + a ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hzle ha2]
    exact mul_le_mul_of_nonneg_left hinner hz
  have hnumle :
      lam * N * (z * (a * (A + B) + a ^ 2 * z)) ≤
        z * lam * N * (a * (A + B) + a ^ 2) := by
    have hLN : 0 ≤ lam * N := mul_nonneg hlam hN
    nlinarith [mul_le_mul_of_nonneg_left hcore hLN]
  have hprod : A * B ≤ (A + a * z) * (B + a * z) := by
    have hA' : A ≤ A + a * z := by nlinarith [mul_nonneg ha hz]
    have hB' : B ≤ B + a * z := by nlinarith [mul_nonneg ha hz]
    calc
      A * B ≤ A * (B + a * z) := mul_le_mul_of_nonneg_left hB' (le_of_lt hA)
      _ ≤ (A + a * z) * (B + a * z) :=
        mul_le_mul_of_nonneg_right hA' (le_of_lt hBz)
  have hden : A ^ 2 * B ^ 2 ≤ A * B * (A + a * z) * (B + a * z) := by
    have hAB : 0 ≤ A * B := mul_nonneg (le_of_lt hA) (le_of_lt hB)
    calc
      A ^ 2 * B ^ 2 = (A * B) * (A * B) := by ring
      _ ≤ (A * B) * ((A + a * z) * (B + a * z)) :=
        mul_le_mul_of_nonneg_left hprod hAB
      _ = A * B * (A + a * z) * (B + a * z) := by ring
  have hrhs : z * (lam * N * (a * (A + B) + a ^ 2) / (A ^ 2 * B ^ 2)) =
      (z * lam * N * (a * (A + B) + a ^ 2)) / (A ^ 2 * B ^ 2) := by ring
  rw [hnum, hrhs, div_le_div_iff₀ hD hD0]
  have hboundNonneg : 0 ≤ z * lam * N * (a * (A + B) + a ^ 2) := by positivity
  calc
    (lam * N * (z * (a * (A + B) + a ^ 2 * z))) * (A ^ 2 * B ^ 2) ≤
        (z * lam * N * (a * (A + B) + a ^ 2)) * (A ^ 2 * B ^ 2) :=
      mul_le_mul_of_nonneg_right hnumle (le_of_lt hD0)
    _ ≤ (z * lam * N * (a * (A + B) + a ^ 2)) *
        (A * B * (A + a * z) * (B + a * z)) :=
      mul_le_mul_of_nonneg_left hden hboundNonneg

/-- A zero discount on an offered product cannot maximize the compactified
objective: move it to a sufficiently small positive discount, so its
`T * exp (-β T)` numerator gain dominates the linear denominator losses in
later stages. -/
theorem compact_boundary_improve {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n)) (hS : Feasible S)
    (x : Fin n → ℝ) (k : Fin m) (i : Fin n)
    (hβ : 0 < β) (hLam : ∀ h, 0 < lam h)
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
    (hxi : x i = 0) (hi : i ∈ S k) :
    ∃ y ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
      compactRevenue α β lam S x < compactRevenue α β lam S y := by
  let a := Real.exp (α i)
  let A := 1 + compactPrefix α x S k
  let B := 1 + compactPrefix α x S k + compactAttraction α x (S k)
  let N := compactNumerator α β S x k
  let Ah (h : Fin m) := 1 + compactPrefix α x S h
  let Bh (h : Fin m) := 1 + compactPrefix α x S h + compactAttraction α x (S h)
  let Nh (h : Fin m) := compactNumerator α β S x h
  let loss (h : Fin m) :=
    lam h * Nh h * (a * (Ah h + Bh h) + a ^ 2) / (Ah h ^ 2 * Bh h ^ 2)
  let C := ∑ h, if k < h then loss h else 0
  have ha : 0 < a := by simp [a, Real.exp_pos]
  have hA : 0 < A := by
    dsimp [A]
    linarith [compactPrefix_nonneg α x S k]
  have hB : 0 < B := by
    dsimp [B]
    have hp := compactPrefix_nonneg α x S k
    have hv := compactAttraction_nonneg α x (S k)
    linarith
  have hN : 0 ≤ N := by
    exact compactNumerator_nonneg α β S x k hβ
  have hAh (h : Fin m) : 0 < Ah h := by
    dsimp [Ah]
    linarith [compactPrefix_nonneg α x S h]
  have hBh (h : Fin m) : 0 < Bh h := by
    dsimp [Bh]
    have hp := compactPrefix_nonneg α x S h
    have hv := compactAttraction_nonneg α x (S h)
    linarith
  have hNh (h : Fin m) : 0 ≤ Nh h := by
    exact compactNumerator_nonneg α β S x h hβ
  have hloss (h : Fin m) : 0 ≤ loss h := by
    dsimp [loss]
    have hLambda0 : 0 ≤ lam h := le_of_lt (hLam h)
    have hN0 := hNh h
    have hA0 := hAh h
    have hB0 := hBh h
    apply div_nonneg
    · positivity
    · positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    apply Finset.sum_nonneg
    intro h hh
    by_cases hkh : k < h
    · simp [hkh]
      exact hloss h
    · simp [hkh]
  obtain ⟨T, z, hzeq, hz, hzle, hgain⟩ :=
    boundary_gain_beats_linear_loss A B N (lam k) a β C hA hB hN
      (hLam k) ha hβ hC
  have hzbox : z ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hz, hzle⟩
  let y := updateDiscount x i z
  have hy : y ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
    exact updateDiscount_mem_box x i z hx hzbox
  have hnumTarget : compactNumerator α β S y k = N + a * (z * T) := by
    rw [show y = updateDiscount x i z by rfl]
    rw [compactNumerator_update α β S x i z k hx hxi hzbox hi]
    change compactNumerator α β S x k + Real.exp (α i) * Real.negMulLog z / β =
      N + a * (z * T)
    have hterm : Real.exp (α i) * Real.negMulLog z / β = a * (z * T) := by
      rw [show Real.exp (α i) * Real.negMulLog z / β =
        Real.exp (α i) * (Real.negMulLog z / β) by ring, hzeq,
        negMulLog_exp_price β T hβ.ne']
    rw [hterm]
  have hdenTarget : compactDenominator α S y k = A * (B + a * z) := by
    rw [show y = updateDiscount x i z by rfl]
    exact compactDenominator_update_target α S x i z k hS hx hxi hzbox hi
  have hdenBase : compactDenominator α S x k = A * B := by
    dsimp [A, B]
    rfl
  have hstageTarget :
      compactStageRevenue α β lam S y k - compactStageRevenue α β lam S x k =
        lam k * (N + a * (z * T)) / (A * (B + a * z)) - lam k * N / (A * B) := by
    simp [compactStageRevenue, hnumTarget, hdenTarget, hdenBase, N]
  let gain := lam k * (N + a * (z * T)) / (A * (B + a * z)) - lam k * N / (A * B)
  have hstageTarget' : compactStageRevenue α β lam S y k -
      compactStageRevenue α β lam S x k = gain := by simpa [gain] using hstageTarget
  have hgain' : gain > C * z := by simpa [gain, mul_comm] using hgain
  have hfutureLoss (h : Fin m) (hkh : k < h) :
      compactStageRevenue α β lam S x h - compactStageRevenue α β lam S y h ≤ z * loss h := by
    have hnot : i ∉ S h := by
      intro hit
      exact (Finset.disjoint_left.mp (hS k h (ne_of_lt hkh))) hi hit
    have hnum : compactNumerator α β S y h = Nh h := by
      rw [show y = updateDiscount x i z by rfl]
      exact compactNumerator_update_of_not_mem α β S x i z h hx hxi hzbox hnot
    have hden : compactDenominator α S y h =
        (Ah h + a * z) * (Bh h + a * z) := by
      rw [show y = updateDiscount x i z by rfl]
      exact compactDenominator_update_future α S x i z k h hkh hS hx hxi hzbox hi
    have hdenBase' : compactDenominator α S x h = Ah h * Bh h := by
      dsimp [Ah, Bh]
      rfl
    have hN' : compactNumerator α β S x h = Nh h := rfl
    have hBound := future_loss_le_linear (Ah h) (Bh h) (Nh h) (lam h) a z
      (hAh h) (hBh h) (hNh h) (le_of_lt (hLam h)) (le_of_lt ha) (le_of_lt hz) hzle
    simpa [compactStageRevenue, hnum, hden, hdenBase', hN', loss, mul_comm, mul_left_comm,
      mul_assoc] using hBound
  have hpastSame (h : Fin m) (hkh : h < k) :
      compactStageRevenue α β lam S y h = compactStageRevenue α β lam S x h := by
    have hnot : i ∉ S h := by
      intro hit
      exact (Finset.disjoint_left.mp (hS k h (ne_of_gt hkh))) hi hit
    have hnum : compactNumerator α β S y h = compactNumerator α β S x h := by
      rw [show y = updateDiscount x i z by rfl]
      exact compactNumerator_update_of_not_mem α β S x i z h hx hxi hzbox hnot
    have hden : compactDenominator α S y h = compactDenominator α S x h := by
      rw [show y = updateDiscount x i z by rfl]
      exact compactDenominator_update_past α S x i z k h hkh hS hx hxi hzbox hi
    simp [compactStageRevenue, hnum, hden]
  have hpoint (h : Fin m) :
      compactStageRevenue α β lam S x h - compactStageRevenue α β lam S y h ≤
        (if k < h then z * loss h else if h = k then -gain else 0) := by
    by_cases heq : h = k
    · subst h
      have hdiff : compactStageRevenue α β lam S x k -
          compactStageRevenue α β lam S y k = -gain := by
        linarith [hstageTarget']
      have hle : compactStageRevenue α β lam S x k -
          compactStageRevenue α β lam S y k ≤ -gain := by rw [hdiff]
      simpa [lt_irrefl] using hle
    · by_cases hkh : k < h
      · simpa [hkh, heq] using hfutureLoss h hkh
      · have hlt : h < k := lt_of_le_of_ne (le_of_not_gt hkh) heq
        have hs := hpastSame h hlt
        have hzero : compactStageRevenue α β lam S x h -
            compactStageRevenue α β lam S y h = 0 := by rw [hs]; ring
        have hle : compactStageRevenue α β lam S x h -
            compactStageRevenue α β lam S y h ≤ 0 := by rw [hzero]
        simpa [hkh, heq] using hle
  have hsumRhs :
      (∑ h, if k < h then z * loss h else if h = k then -gain else 0) = z * C - gain := by
    calc
      (∑ h, if k < h then z * loss h else if h = k then -gain else 0) =
          ∑ h, ((if k < h then z * loss h else 0) + if h = k then -gain else 0) := by
            apply Finset.sum_congr rfl
            intro h hh
            by_cases hkh : k < h
            · have hne : h ≠ k := Ne.symm (ne_of_lt hkh)
              simp [hkh, hne]
            · simp [hkh]
      _ = (∑ h, if k < h then z * loss h else 0) +
          (∑ h, if h = k then -gain else 0) := by rw [Finset.sum_add_distrib]
      _ = z * C - gain := by
          have hfirst : (∑ h, if k < h then z * loss h else 0) = z * C := by
            dsimp [C]
            calc
              (∑ h, if k < h then z * loss h else 0) =
                  ∑ h, z * (if k < h then loss h else 0) := by
                    apply Finset.sum_congr rfl
                    intro h hh
                    by_cases hkh : k < h <;> simp [hkh]
              _ = z * (∑ h, if k < h then loss h else 0) := by rw [Finset.mul_sum]
          have hsecond : (∑ h, if h = k then -gain else 0) = -gain := by
            rw [Finset.sum_ite_eq']
            simp
          rw [hfirst, hsecond]
          ring
  have hdiff : compactRevenue α β lam S x - compactRevenue α β lam S y < 0 := by
    rw [compactRevenue_eq_compactStageRevenue, compactRevenue_eq_compactStageRevenue,
      ← Finset.sum_sub_distrib]
    calc
      (∑ h, (compactStageRevenue α β lam S x h - compactStageRevenue α β lam S y h)) ≤
          ∑ h, (if k < h then z * loss h else if h = k then -gain else 0) :=
        Finset.sum_le_sum (fun h hh => hpoint h)
      _ = z * C - gain := hsumRhs
      _ < 0 := by nlinarith [hgain']
  refine ⟨y, hy, ?_⟩
  linarith

/-- At a zero discount, a finite price creates a `T * exp (-β T)` numerator
term. For any fixed linear loss bound, taking `T` large makes this term win.
This is the scalar boundary perturbation behind the missing attainment step. -/
theorem boundary_gain_beats_linear_loss_late
    (A B N lam a β C : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hN : 0 ≤ N)
    (hlam : 0 < lam) (ha : 0 < a) (hβ : 0 < β) (hC : 0 ≤ C) :
    ∃ T z : ℝ, 0 < z ∧ z ≤ 1 ∧
      lam * (N + a * (z * T)) / (A * (B + a * z)) -
          lam * N / (A * B) > C * z := by
  let T := N / B + (C + 1) * A * (B + a) / (lam * a)
  let z := Real.exp (-β * T)
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hz : 0 < z := Real.exp_pos _
  have hzle : z ≤ 1 := by
    dsimp [z]
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hscale :
      (lam * (N + a * (z * T)) / (A * (B + a * z)) -
        lam * N / (A * B)) =
      z * (C + 1) * (B + a) / (B + a * z) := by
    dsimp [T]
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hlam,
      ne_of_gt ha, ne_of_gt hβ]
    <;> ring
  refine ⟨T, z, hz, hzle, ?_⟩
  rw [hscale]
  have hden : 0 < B + a * z := by positivity
  have hratio : 1 ≤ (B + a) / (B + a * z) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hfactor : 0 ≤ z * (C + 1) :=
    mul_nonneg (le_of_lt hz) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hratio hfactor
  have hstrict : C * z < z * (C + 1) := by nlinarith
  calc
    C * z < z * (C + 1) := hstrict
    _ ≤ z * (C + 1) * ((B + a) / (B + a * z)) := by
      simpa [mul_assoc] using hmul
    _ = z * (C + 1) * (B + a) / (B + a * z) := by ring

theorem future_loss_le_linear_late
    (A B N lam a z : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hN : 0 ≤ N)
    (hlam : 0 ≤ lam) (ha : 0 ≤ a) (hz : 0 ≤ z) (hzle : z ≤ 1) :
    lam * N / (A * B) - lam * N / ((A + a * z) * (B + a * z)) ≤
      z * (lam * N * (a * (A + B) + a ^ 2) / (A ^ 2 * B ^ 2)) := by
  have hAz : 0 < A + a * z := by positivity
  have hBz : 0 < B + a * z := by positivity
  have hD : 0 < A * B * (A + a * z) * (B + a * z) := by positivity
  have hD0 : 0 < A ^ 2 * B ^ 2 := by positivity
  have hnum :
      lam * N / (A * B) - lam * N / ((A + a * z) * (B + a * z)) =
        (lam * N * (z * (a * (A + B) + a ^ 2 * z))) /
          (A * B * (A + a * z) * (B + a * z)) := by
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hAz, ne_of_gt hBz]
    <;> ring
  have hcore : z * (a * (A + B) + a ^ 2 * z) ≤
      z * (a * (A + B) + a ^ 2) := by
    have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
    have hinner : a * (A + B) + a ^ 2 * z ≤ a * (A + B) + a ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hzle ha2]
    exact mul_le_mul_of_nonneg_left hinner hz
  have hnumle :
      lam * N * (z * (a * (A + B) + a ^ 2 * z)) ≤
        z * lam * N * (a * (A + B) + a ^ 2) := by
    have hLN : 0 ≤ lam * N := mul_nonneg hlam hN
    nlinarith [mul_le_mul_of_nonneg_left hcore hLN]
  have hprod : A * B ≤ (A + a * z) * (B + a * z) := by
    have hA' : A ≤ A + a * z := by nlinarith [mul_nonneg ha hz]
    have hB' : B ≤ B + a * z := by nlinarith [mul_nonneg ha hz]
    calc
      A * B ≤ A * (B + a * z) := mul_le_mul_of_nonneg_left hB' (le_of_lt hA)
      _ ≤ (A + a * z) * (B + a * z) :=
        mul_le_mul_of_nonneg_right hA' (le_of_lt hBz)
  have hden : A ^ 2 * B ^ 2 ≤ A * B * (A + a * z) * (B + a * z) := by
    have hAB : 0 ≤ A * B := mul_nonneg (le_of_lt hA) (le_of_lt hB)
    calc
      A ^ 2 * B ^ 2 = (A * B) * (A * B) := by ring
      _ ≤ (A * B) * ((A + a * z) * (B + a * z)) :=
        mul_le_mul_of_nonneg_left hprod hAB
      _ = A * B * (A + a * z) * (B + a * z) := by ring
  have hrhs : z * (lam * N * (a * (A + B) + a ^ 2) / (A ^ 2 * B ^ 2)) =
      (z * lam * N * (a * (A + B) + a ^ 2)) / (A ^ 2 * B ^ 2) := by ring
  rw [hnum, hrhs, div_le_div_iff₀ hD hD0]
  have hboundNonneg : 0 ≤ z * lam * N * (a * (A + B) + a ^ 2) := by positivity
  calc
    (lam * N * (z * (a * (A + B) + a ^ 2 * z))) * (A ^ 2 * B ^ 2) ≤
        (z * lam * N * (a * (A + B) + a ^ 2)) * (A ^ 2 * B ^ 2) :=
      mul_le_mul_of_nonneg_right hnumle (le_of_lt hD0)
    _ ≤ (z * lam * N * (a * (A + B) + a ^ 2)) *
        (A * B * (A + a * z) * (B + a * z)) :=
      mul_le_mul_of_nonneg_left hden hboundNonneg

end GaoImpatientMNL.Pricing.Attempt

open scoped BigOperators

theorem solution {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ)
    (h : GaoImpatientMNL.Pricing.Parameters (n := n) β lam)
    (S : Fin m → Finset (Fin n)) (hS : GaoImpatientMNL.Pricing.Feasible S) :
    ∃ p : Fin n → ℝ, GaoImpatientMNL.Pricing.IsPricingMax α β lam S p ∧
      ∀ k, ∀ i ∈ S k, ∀ j ∈ S k, p i = p j := by
  rcases h with ⟨_, _, hβ, _, hLam, _⟩
  obtain ⟨x, hxbox, hmax⟩ :=
    GaoImpatientMNL.Pricing.Attempt.compactified_maximum_exists α β lam S
  have hxpos : ∀ k i, i ∈ S k → 0 < x i := by
    intro k i hi
    by_contra hpos
    have hxi : x i = 0 := by
      have hnonneg : 0 ≤ x i := (hxbox i (Set.mem_univ i)).1
      have hnotpos : ¬ 0 < x i := hpos
      linarith
    obtain ⟨y, hybox, hygain⟩ :=
      GaoImpatientMNL.Pricing.Attempt.compact_boundary_improve
        α β lam S hS x k i hβ hLam hxbox hxi hi
    have hmax' := hmax hybox
    change GaoImpatientMNL.Pricing.Attempt.compactRevenue α β lam S y ≤
      GaoImpatientMNL.Pricing.Attempt.compactRevenue α β lam S x at hmax'
    linarith
  have hp := GaoImpatientMNL.Pricing.Attempt.compactified_maximum_gives_pricing_max
    α β lam S hβ hLam x hxbox hmax hxpos
  exact GaoImpatientMNL.Pricing.Attempt.equalized_maximizer_of_maximizer
    α β lam S hS hβ hLam (GaoImpatientMNL.Pricing.Attempt.priceOfDiscount β x) hp

#print axioms solution
