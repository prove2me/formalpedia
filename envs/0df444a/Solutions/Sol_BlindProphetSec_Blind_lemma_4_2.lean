-- Prove2me | solution 1 for BlindProphetSec.Blind.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:17:13.640205+00:00
-- url     : https://prove2.me/submissions/67ad8f13-8331-48ac-b6e7-41794eaaa238

import Mathlib
import Definitions.Def_BlindProphetSec_Blind_Setting

open MeasureTheory

namespace BPSLem42

open BlindProphetSec.Blind

/-- Inequality (4.4) of the paper, in the variables `x_i = F_i(τ₁)`, `y_i = F_i(t)`, `λ = k/n`. -/
lemma pair_ineq (l x1 x2 y1 y2 : ℝ) (hl0 : 0 ≤ l) (hl : l ≤ 1 / 2)
    (hy1 : 0 ≤ y1) (hyx1 : y1 ≤ x1) (hx1 : x1 ≤ 1)
    (hy2 : 0 ≤ y2) (hyx2 : y2 ≤ x2) (hx2 : x2 ≤ 1) :
    (1 - y1 * y2) / (1 - l * (1 - x1 * x2)) ≤
      (1 - y1) / (1 - l * (1 - x1)) + (1 - y2) / (1 - l * (1 - x2)) := by
  have hx1' : 0 ≤ x1 := le_trans hy1 hyx1
  have hx2' : 0 ≤ x2 := le_trans hy2 hyx2
  have hp : 0 ≤ x1 * x2 := mul_nonneg hx1' hx2'
  have hp1 : x1 * x2 ≤ 1 := by nlinarith
  have hD1 : 0 < 1 - l * (1 - x1) := by nlinarith
  have hD2 : 0 < 1 - l * (1 - x2) := by nlinarith
  have hD12 : 0 < 1 - l * (1 - x1 * x2) := by nlinarith
  rw [div_add_div _ _ hD1.ne' hD2.ne', div_le_div_iff₀ hD12 (mul_pos hD1 hD2)]
  have key : ((1 - y1) * (1 - l * (1 - x2)) + (1 - l * (1 - x1)) * (1 - y2)) *
        (1 - l * (1 - x1 * x2)) - (1 - y1 * y2) * ((1 - l * (1 - x1)) * (1 - l * (1 - x2))) =
      (1 - y1) * (1 - y2) * (1 - 2 * l + l ^ 2 * (1 - x1 * x2)) +
        l * x1 * (1 - l * (1 - x2)) * (1 - y1) * (x2 - y2) +
        l * x2 * (1 - l * (1 - x1)) * (1 - y2) * (x1 - y1) := by ring
  have t1 : 0 ≤ (1 - y1) * (1 - y2) * (1 - 2 * l + l ^ 2 * (1 - x1 * x2)) := by
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith))
    have : 0 ≤ l ^ 2 * (1 - x1 * x2) := mul_nonneg (sq_nonneg l) (by linarith)
    linarith
  have t2 : 0 ≤ l * x1 * (1 - l * (1 - x2)) * (1 - y1) * (x2 - y2) := by
    apply mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hl0 hx1') hD2.le) (by linarith))
    linarith
  have t3 : 0 ≤ l * x2 * (1 - l * (1 - x1)) * (1 - y2) * (x1 - y1) := by
    apply mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hl0 hx2') hD1.le) (by linarith))
    linarith
  linarith

/-- Iterating (4.4): `Σ_i (1 - y_i)/(1 - λ(1 - x_i)) ≥ (1 - ∏ y_i)/(1 - λ(1 - ∏ x_i))`. -/
lemma sum_ineq {ι : Type*} (S : Finset ι) (l : ℝ) (hl0 : 0 ≤ l) (hl : l ≤ 1 / 2)
    (x y : ι → ℝ) (hy : ∀ i, 0 ≤ y i) (hyx : ∀ i, y i ≤ x i) (hx : ∀ i, x i ≤ 1) :
    (1 - ∏ i ∈ S, y i) / (1 - l * (1 - ∏ i ∈ S, x i)) ≤
      ∑ i ∈ S, (1 - y i) / (1 - l * (1 - x i)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have hY0 : 0 ≤ ∏ i ∈ S, y i := Finset.prod_nonneg fun i _ => hy i
    have hYX : ∏ i ∈ S, y i ≤ ∏ i ∈ S, x i :=
      Finset.prod_le_prod (fun i _ => hy i) (fun i _ => hyx i)
    have hX1 : ∏ i ∈ S, x i ≤ 1 :=
      Finset.prod_le_one (fun i _ => le_trans (hy i) (hyx i)) (fun i _ => hx i)
    have := pair_ineq l (x j) (∏ i ∈ S, x i) (y j) (∏ i ∈ S, y i) hl0 hl (hy j) (hyx j) (hx j)
      hY0 hYX hX1
    linarith

lemma ioi_toReal (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    (ν (Set.Ioi x)).toReal = 1 - (ν (Set.Iic x)).toReal := by
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
  simp

lemma pmaxGT_eq {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (x : ℝ) :
    PmaxGT μ x = 1 - ∏ i, (μ i (Set.Iic x)).toReal := by
  unfold PmaxGT
  have hset : {v : Fin n → ℝ | ∃ i, x < v i} = (Set.univ.pi fun _ => Set.Iic x)ᶜ := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Iic, not_forall, not_le]
  rw [hset, prob_compl_eq_one_sub (MeasurableSet.univ_pi fun _ => measurableSet_Iic),
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, Measure.pi_pi,
    ENNReal.toReal_prod]
  simp

end BPSLem42

open BlindProphetSec.Blind BPSLem42 in
theorem solution {n : ℕ} [NeZero n] (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (τ : Fin n → ℝ) (hτ : ∀ l, τ l ≤ τ 0) (t : ℝ) (ht : t < τ 0) (k : ℕ) (hk : 2 * k ≤ n) :
    PmaxGT μ t / (1 - (k : ℝ) / n * PmaxGT μ (τ 0)) ≤
      ∑ i : Fin n, (μ i (Set.Ioi t)).toReal /
        (1 - (1 / (n : ℝ)) * ∑ l ∈ Finset.univ.filter (fun l : Fin n => l.val < k),
          (μ i (Set.Ioi (τ l))).toReal) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set lam : ℝ := (k : ℝ) / n with hlam
  have hl0 : 0 ≤ lam := by positivity
  have hl : lam ≤ 1 / 2 := by
    rw [hlam, div_le_iff₀ hn]
    have : (2 * k : ℝ) ≤ n := by exact_mod_cast hk
    linarith
  set x : Fin n → ℝ := fun i => (μ i (Set.Iic (τ 0))).toReal with hx
  set y : Fin n → ℝ := fun i => (μ i (Set.Iic t)).toReal with hy
  have hy0 : ∀ i, 0 ≤ y i := fun i => ENNReal.toReal_nonneg
  have hyx : ∀ i, y i ≤ x i := fun i =>
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.mpr ht.le))
  have hx1 : ∀ i, x i ≤ 1 := fun i => by
    simp only [hx]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  rw [pmaxGT_eq, pmaxGT_eq]
  refine le_trans (sum_ineq Finset.univ lam hl0 hl x y hy0 hyx hx1) ?_
  apply Finset.sum_le_sum
  intro i _
  have hcard : (Finset.univ.filter (fun l : Fin n => l.val < k)).card = k := by
    rw [Fin.card_filter_val_lt]; omega
  set s := ∑ l ∈ Finset.univ.filter (fun l : Fin n => l.val < k), (μ i (Set.Ioi (τ l))).toReal
    with hs
  have hs_lo : (k : ℝ) * (1 - x i) ≤ s := by
    have : ∑ l ∈ Finset.univ.filter (fun l : Fin n => l.val < k), (1 - x i) ≤ s := by
      apply Finset.sum_le_sum
      intro l _
      rw [hx]; simp only
      rw [← ioi_toReal]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ioi_subset_Ioi (hτ l)))
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at this
    exact this
  have hs_hi : s ≤ k := by
    have : s ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin n => l.val < k), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro l _
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one] at this
    exact this
  have hD' : 0 < 1 - 1 / (n : ℝ) * s := by
    have : 1 / (n : ℝ) * s ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hn]
      have : (2 * k : ℝ) ≤ n := by exact_mod_cast hk
      linarith
    linarith
  have hle : 1 - 1 / (n : ℝ) * s ≤ 1 - lam * (1 - x i) := by
    have : lam * (1 - x i) ≤ 1 / (n : ℝ) * s := by
      rw [hlam, div_mul_eq_mul_div, one_div_mul_eq_div, div_le_div_iff_of_pos_right hn]
      exact hs_lo
    linarith
  rw [ioi_toReal]
  exact div_le_div_of_nonneg_left (by linarith [hyx i, hx1 i]) hD' hle
