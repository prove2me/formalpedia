-- Prove2me | solution 1 for Formalism.HermitianLattices.FormalDegreeBoundsAlt.explicit_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:23:30.438657+00:00
-- url     : https://prove2.me/submissions/895240a7-8901-42c2-99c6-a23fa6632fa1

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_UnitaryConjugateDiagonalMoments
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_IndicatorValueMemUnitInterval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.FormalDegreeBoundsAlt
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
private lemma g5w7_log_sub_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Real.log p - Real.log q ≤ (p - q) / q := by
  rw [← Real.log_div hp.ne' hq.ne']
  have h1 := Real.log_le_sub_one_of_pos (div_pos hp hq)
  have h2 : p / q - 1 = (p - q) / q := by field_simp
  linarith
private lemma g5w7_vandN_succ (x : ℕ → ℝ) (N : ℕ) :
    vandN x (N + 1) = vandN x N * ∏ i ∈ range N, (x i - x N) := by
  unfold vandN
  rw [prod_range_succ, Ico_self, prod_empty, mul_one, ← prod_mul_distrib]
  refine prod_congr rfl fun i hi => ?_
  rw [prod_Ico_succ_top (by have := mem_range.1 hi; omega)]
private lemma g5w7_vandN_head (x : ℕ → ℝ) (N : ℕ) :
    vandN x (N + 1) = (∏ j ∈ range N, (x 0 - x (j + 1))) * vandN (fun i => x (i + 1)) N := by
  unfold vandN
  rw [prod_range_succ', mul_comm]
  congr 1
  · rw [prod_Ico_eq_prod_range]
    refine prod_congr rfl fun j _ => ?_
    rw [add_comm (0 + 1) j]
  · refine prod_congr rfl fun i _ => ?_
    rw [← prod_Ico_add' (fun j => x (i + 1) - x j) (i + 1) N 1]
private lemma g5w7_vandN_congr {x y : ℕ → ℝ} {N : ℕ} (h : ∀ i, i < N → x i = y i) :
    vandN x N = vandN y N := by
  unfold vandN
  refine prod_congr rfl fun i hi => prod_congr rfl fun j hj => ?_
  rw [h i (mem_range.1 hi), h j (mem_Ico.1 hj).2]
private lemma g5w7_log_vandN (x : ℕ → ℝ) (N : ℕ) (h : ∀ i j, i < j → j < N → x i - x j ≠ 0) :
    Real.log (vandN x N) = ∑ i ∈ range N, ∑ j ∈ Ico (i + 1) N, Real.log (x i - x j) := by
  unfold vandN
  rw [Real.log_prod]
  · refine sum_congr rfl fun i _ => ?_
    rw [Real.log_prod]
    intro j hj
    rw [mem_Ico] at hj
    exact h i j (by omega) hj.2
  · intro i _
    rw [prod_ne_zero_iff]
    intro j hj
    rw [mem_Ico] at hj
    exact h i j (by omega) hj.2
private lemma g5w7_H_le (n : ℕ) : ∑ d ∈ range n, 1 / ((d : ℝ) + 1) ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  have e : ((harmonic n : ℚ) : ℝ) = ∑ d ∈ range n, 1 / ((d : ℝ) + 1) := by
    unfold harmonic
    push_cast
    refine sum_congr rfl fun d _ => ?_
    rw [one_div]
  rw [e] at h
  exact h
private lemma g5w7_H_mono {a n : ℕ} (h : a ≤ n) :
    ∑ d ∈ range a, 1 / ((d : ℝ) + 1) ≤ ∑ d ∈ range n, 1 / ((d : ℝ) + 1) := by
  refine sum_le_sum_of_subset_of_nonneg (range_subset_range.2 h) fun d _ _ => ?_
  positivity
private lemma g5w7_pair_sum_le (n : ℕ) (C : ℝ) (hC : 0 ≤ C) (a : ℕ → ℕ → ℝ)
    (h : ∀ i j, i < j → j < n → a i j ≤ C / ((j : ℝ) - i)) :
    ∑ i ∈ range n, ∑ j ∈ Ico (i + 1) n, a i j ≤ C * n * (1 + Real.log n) := by
  have inner : ∀ i ∈ range n, ∑ j ∈ Ico (i + 1) n, a i j ≤ C * (1 + Real.log n) := by
    intro i _
    calc ∑ j ∈ Ico (i + 1) n, a i j ≤ ∑ j ∈ Ico (i + 1) n, C / ((j : ℝ) - i) := by
          refine sum_le_sum fun j hj => ?_
          rw [mem_Ico] at hj
          exact h i j (by omega) hj.2
      _ = C * ∑ d ∈ range (n - (i + 1)), 1 / ((d : ℝ) + 1) := by
          rw [sum_Ico_eq_sum_range, mul_sum]
          refine sum_congr rfl fun d _ => ?_
          push_cast
          rw [mul_one_div]
          congr 1
          ring
      _ ≤ C * (1 + Real.log n) := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          exact (g5w7_H_mono (by omega)).trans (g5w7_H_le n)
  calc ∑ i ∈ range n, ∑ j ∈ Ico (i + 1) n, a i j ≤ ∑ _i ∈ range n, C * (1 + Real.log n) := sum_le_sum inner
    _ = C * n * (1 + Real.log n) := by
        rw [sum_const, card_range, nsmul_eq_mul]; ring
private lemma cloudV_sub_cloudV (c Δ : ℝ) (i j : ℕ) :
    cloudV c Δ i - cloudV c Δ j = 4 * Δ * ((j : ℝ) - i) := by
  unfold cloudV; ring
private lemma g5w7_word_diff (c Δ : ℝ) (δ : ℕ → ℕ) (i j : ℕ) :
    wordU c Δ δ i - wordU c Δ δ j = 4 * Δ * ((j : ℝ) - i) + ((δ j : ℝ) - δ i) * Δ := by
  unfold wordU cloudV; ring
private lemma indicator_value_mem_unit_interval {δ : ℕ → ℕ} (hδ : ∀ l, δ l ≤ 1) (l : ℕ) : (0 : ℝ) ≤ δ l ∧ (δ l : ℝ) ≤ 1 :=
  ⟨Nat.cast_nonneg _, by exact_mod_cast hδ l⟩
private lemma g5w7_gap {i j : ℕ} (h : i < j) : (1 : ℝ) ≤ (j : ℝ) - i := by
  have : ((i + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast h
  push_cast at this
  linarith
private lemma g5w7_cloud_pos (c : ℝ) {Δ : ℝ} (hΔ : 0 < Δ) {i j : ℕ} (h : i < j) :
    0 < cloudV c Δ i - cloudV c Δ j := by
  rw [cloudV_sub_cloudV]
  have := g5w7_gap h
  positivity
private lemma g5w7_word_pos (c : ℝ) {Δ : ℝ} (hΔ : 0 < Δ) {δ : ℕ → ℕ} (hδ : ∀ l, δ l ≤ 1) {i j : ℕ} (h : i < j) :
    0 < wordU c Δ δ i - wordU c Δ δ j := by
  rw [g5w7_word_diff]
  have h1 := g5w7_gap h
  have hi := indicator_value_mem_unit_interval hδ i
  have hj := indicator_value_mem_unit_interval hδ j
  nlinarith [mul_le_mul_of_nonneg_left h1 hΔ.le, mul_nonneg hΔ.le hj.1,
    mul_le_mul_of_nonneg_left hi.2 hΔ.le]
private lemma g5w7_cloud_upper (n : ℕ) (c : ℝ) {Δ : ℝ} (hΔ : 0 < Δ) {δ : ℕ → ℕ} (hδ : ∀ l, δ l ≤ 1) :
    Real.log (vandN (wordU c Δ δ) n) - Real.log (vandN (cloudV c Δ) n) ≤ 1 / 4 * n * (1 + Real.log n) := by
  rw [g5w7_log_vandN _ _ fun i j hij _ => (g5w7_word_pos c hΔ hδ hij).ne',
    g5w7_log_vandN _ _ fun i j hij _ => (g5w7_cloud_pos c hΔ hij).ne', ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  refine g5w7_pair_sum_le n (1 / 4) (by norm_num) _ fun i j hij _ => ?_
  refine (g5w7_log_sub_le (g5w7_word_pos c hΔ hδ hij) (g5w7_cloud_pos c hΔ hij)).trans ?_
  have h1 := g5w7_gap hij
  have hi := indicator_value_mem_unit_interval hδ i
  have hj := indicator_value_mem_unit_interval hδ j
  have hc := g5w7_cloud_pos c hΔ hij
  rw [div_le_div_iff₀ hc (by linarith)]
  rw [g5w7_word_diff, cloudV_sub_cloudV]
  have hD : 0 ≤ Δ * ((j : ℝ) - i) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (show (δ j : ℝ) - δ i ≤ 1 by linarith) hD]
private lemma g5w7_cloud_lower (n : ℕ) (c : ℝ) {Δ : ℝ} (hΔ : 0 < Δ) {δ : ℕ → ℕ} (hδ : ∀ l, δ l ≤ 1) :
    Real.log (vandN (cloudV c Δ) n) - Real.log (vandN (wordU c Δ δ) n) ≤ 1 / 3 * n * (1 + Real.log n) := by
  rw [g5w7_log_vandN _ _ fun i j hij _ => (g5w7_word_pos c hΔ hδ hij).ne',
    g5w7_log_vandN _ _ fun i j hij _ => (g5w7_cloud_pos c hΔ hij).ne', ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  refine g5w7_pair_sum_le n (1 / 3) (by norm_num) _ fun i j hij _ => ?_
  refine (g5w7_log_sub_le (g5w7_cloud_pos c hΔ hij) (g5w7_word_pos c hΔ hδ hij)).trans ?_
  have h1 := g5w7_gap hij
  have hi := indicator_value_mem_unit_interval hδ i
  have hj := indicator_value_mem_unit_interval hδ j
  have hw := g5w7_word_pos c hΔ hδ hij
  rw [div_le_div_iff₀ hw (by linarith)]
  rw [g5w7_word_diff, cloudV_sub_cloudV]

  have hD : 0 ≤ Δ * (1 + 3 * ((j : ℝ) - i)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (show (-1 : ℝ) ≤ (δ j : ℝ) - δ i by linarith) hD,
    mul_le_mul_of_nonneg_left h1 hΔ.le]
private lemma g5w7_nlog_nonneg (n : ℕ) : 0 ≤ (n : ℝ) * (1 + Real.log n) := by
  have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  positivity
private lemma g5w7_cloud_two (n : ℕ) (c : ℝ) {Δ : ℝ} (hΔ : 0 < Δ) {δ δ' : ℕ → ℕ} (hδ : ∀ l, δ l ≤ 1)
    (hδ' : ∀ l, δ' l ≤ 1) :
    |Real.log (vandN (wordU c Δ δ) n) - Real.log (vandN (wordU c Δ δ') n)| ≤
      7 / 12 * n * (1 + Real.log n) := by
  have a1 := g5w7_cloud_upper n c hΔ hδ
  have a2 := g5w7_cloud_lower n c hΔ hδ
  have b1 := g5w7_cloud_upper n c hΔ hδ'
  have b2 := g5w7_cloud_lower n c hΔ hδ'
  rw [abs_le]
  constructor <;> linarith
private lemma g5w7_colU_zero (n : ℕ) (c Δ u0 uk : ℝ) (δ : ℕ → ℕ) : colU (n + 2) c Δ δ u0 uk 0 = u0 := by
  simp [colU]
private lemma g5w7_colU_last (n : ℕ) (c Δ u0 uk : ℝ) (δ : ℕ → ℕ) : colU (n + 2) c Δ δ u0 uk (n + 1) = uk := by
  simp [colU]
private lemma g5w7_colU_mid (n : ℕ) (c Δ u0 uk : ℝ) (δ : ℕ → ℕ) {i : ℕ} (h : i < n) :
    colU (n + 2) c Δ δ u0 uk (i + 1) = wordU c Δ δ i := by
  unfold colU
  rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
private lemma g5w7_colU_vand (n : ℕ) (c Δ u0 uk : ℝ) (δ : ℕ → ℕ) :
    vandN (colU (n + 2) c Δ δ u0 uk) (n + 2) =
      ((∏ j ∈ range n, (u0 - wordU c Δ δ j)) * (u0 - uk)) *
        (vandN (wordU c Δ δ) n * ∏ i ∈ range n, (wordU c Δ δ i - uk)) := by
  rw [g5w7_vandN_head, g5w7_vandN_succ, prod_range_succ, g5w7_colU_zero, g5w7_colU_last]
  congr 1
  · congr 1
    exact prod_congr rfl fun j hj => by rw [g5w7_colU_mid n c Δ u0 uk δ (mem_range.1 hj)]
  · congr 1
    · exact g5w7_vandN_congr fun i hi => g5w7_colU_mid n c Δ u0 uk δ hi
    · exact prod_congr rfl fun j hj => by rw [g5w7_colU_mid n c Δ u0 uk δ (mem_range.1 hj)]
private lemma g5w7_vandN_pos {x : ℕ → ℝ} {N : ℕ} (h : ∀ i j, i < j → j < N → 0 < x i - x j) : 0 < vandN x N := by
  unfold vandN
  refine prod_pos fun i _ => prod_pos fun j hj => ?_
  rw [mem_Ico] at hj
  exact h i j (by omega) hj.2
private lemma g5w7_colU_log (n : ℕ) (c : ℝ) {Δ : ℝ} (u0 uk : ℝ) {δ : ℕ → ℕ} (hΔ : 0 < Δ) (hδ : ∀ l, δ l ≤ 1)
    (h1 : ∀ j, j < n → 0 < u0 - wordU c Δ δ j) (h2 : u0 - uk ≠ 0) (h3 : ∀ j, j < n → 0 < wordU c Δ δ j - uk) :
    Real.log (vandN (colU (n + 2) c Δ δ u0 uk) (n + 2)) =
      (∑ j ∈ range n, Real.log (u0 - wordU c Δ δ j)) + Real.log (u0 - uk) +
        (Real.log (vandN (wordU c Δ δ) n) + ∑ j ∈ range n, Real.log (wordU c Δ δ j - uk)) := by
  have p1 : 0 < ∏ j ∈ range n, (u0 - wordU c Δ δ j) := prod_pos fun j hj => h1 j (mem_range.1 hj)
  have p3 : 0 < ∏ j ∈ range n, (wordU c Δ δ j - uk) := prod_pos fun j hj => h3 j (mem_range.1 hj)
  have pv : 0 < vandN (wordU c Δ δ) n := g5w7_vandN_pos fun i j hij _ => g5w7_word_pos c hΔ hδ hij
  rw [g5w7_colU_vand, Real.log_mul (mul_ne_zero p1.ne' h2) (mul_ne_zero pv.ne' p3.ne'),
    Real.log_mul p1.ne' h2, Real.log_mul pv.ne' p3.ne',
    Real.log_prod fun j hj => (h1 j (mem_range.1 hj)).ne', Real.log_prod fun j hj => (h3 j (mem_range.1 hj)).ne']
private lemma g5w7_nlog_mono {n k : ℕ} (h : n ≤ k) : (n : ℝ) * (1 + Real.log n) ≤ (k : ℝ) * (1 + Real.log k) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using g5w7_nlog_nonneg k
  · have h1 : (n : ℝ) ≤ k := by exact_mod_cast h
    have h2 : Real.log n ≤ Real.log k := Real.log_le_log (by exact_mod_cast hn) h1
    have h3 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have h4 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_le_mul h1 (show 1 + Real.log n ≤ 1 + Real.log k by linarith) (by linarith) (by linarith)]
private lemma g5w7_term_le {p q Δ K : ℝ} (hΔ : 0 < Δ) (hK : 0 < K) (hq : K * Δ ≤ q) (hpq : p - q ≤ Δ) (hp : 0 < p) :
    Real.log p - Real.log q ≤ 1 / K := by
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  refine (g5w7_log_sub_le hp hq0).trans ?_
  rw [div_le_div_iff₀ hq0 hK]
  nlinarith [mul_le_mul_of_nonneg_right hpq hK.le]
private lemma g5w7_var_one (n : ℕ) (c : ℝ) {Δ : ℝ} (u0 uk : ℝ) {δ δ' : ℕ → ℕ} (hΔ : 0 < Δ) (hδ : ∀ l, δ l ≤ 1)
    (hδ' : ∀ l, δ' l ≤ 1) (hu0 : 4 * ((n : ℝ) + 2) * Δ ≤ u0 - cloudV c Δ 0)
    (hq : ∀ e : ℕ → ℕ, (∀ l, e l ≤ 1) → ∀ l, l < n → 3 * Δ ≤ wordU c Δ e l - uk) (hz : u0 - uk ≠ 0) :
    Real.log (vandN (colU (n + 2) c Δ δ u0 uk) (n + 2)) - Real.log (vandN (colU (n + 2) c Δ δ' u0 uk) (n + 2)) ≤
      7 / 12 * n * (1 + Real.log n) + 1 / 4 + (n : ℝ) / 3 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlow : ∀ e : ℕ → ℕ, (∀ l, e l ≤ 1) → ∀ l, 4 * ((n : ℝ) + 2) * Δ ≤ u0 - wordU c Δ e l := by
    intro e he l
    have h1 := indicator_value_mem_unit_interval he l
    have h2 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have h3 : 0 ≤ (e l : ℝ) * Δ := mul_nonneg h1.1 hΔ.le
    have h4 : 0 ≤ 4 * Δ * (l : ℝ) := by positivity
    unfold wordU
    unfold cloudV at hu0 ⊢
    simp only [Nat.cast_zero, mul_zero, sub_zero] at hu0
    linarith
  have hK : 0 < 4 * ((n : ℝ) + 2) := by positivity
  have hKΔ : 0 < 4 * ((n : ℝ) + 2) * Δ := by positivity
  have h3Δ : 0 < 3 * Δ := by positivity
  rw [g5w7_colU_log n c u0 uk hΔ hδ (fun j _ => lt_of_lt_of_le hKΔ (hlow δ hδ j)) hz
      (fun j hj => lt_of_lt_of_le h3Δ (hq δ hδ j hj)),
    g5w7_colU_log n c u0 uk hΔ hδ' (fun j _ => lt_of_lt_of_le hKΔ (hlow δ' hδ' j)) hz
      (fun j hj => lt_of_lt_of_le h3Δ (hq δ' hδ' j hj))]
  have A : (∑ j ∈ range n, Real.log (u0 - wordU c Δ δ j)) - ∑ j ∈ range n, Real.log (u0 - wordU c Δ δ' j) ≤ 1 / 4 := by
    rw [← sum_sub_distrib]
    calc ∑ j ∈ range n, (Real.log (u0 - wordU c Δ δ j) - Real.log (u0 - wordU c Δ δ' j))
        ≤ ∑ _j ∈ range n, 1 / (4 * ((n : ℝ) + 2)) := by
          refine sum_le_sum fun j _ => ?_
          refine g5w7_term_le hΔ hK (hlow δ' hδ' j) ?_ (lt_of_lt_of_le hKΔ (hlow δ hδ j))
          have h1 := indicator_value_mem_unit_interval hδ j
          have h2 := indicator_value_mem_unit_interval hδ' j
          unfold wordU
          nlinarith [mul_le_mul_of_nonneg_right h1.2 hΔ.le, mul_nonneg h2.1 hΔ.le]
      _ = (n : ℝ) / (4 * ((n : ℝ) + 2)) := by
          rw [sum_const, card_range, nsmul_eq_mul, mul_one_div]
      _ ≤ 1 / 4 := by
          rw [div_le_div_iff₀ hK (by norm_num)]
          linarith
  have B : (∑ j ∈ range n, Real.log (wordU c Δ δ j - uk)) - ∑ j ∈ range n, Real.log (wordU c Δ δ' j - uk) ≤ (n : ℝ) / 3 := by
    rw [← sum_sub_distrib]
    calc ∑ j ∈ range n, (Real.log (wordU c Δ δ j - uk) - Real.log (wordU c Δ δ' j - uk))
        ≤ ∑ _j ∈ range n, 1 / (3 : ℝ) := by
          refine sum_le_sum fun j hj => ?_
          have hj' := mem_range.1 hj
          refine g5w7_term_le hΔ (by norm_num) (hq δ' hδ' j hj') ?_ (lt_of_lt_of_le h3Δ (hq δ hδ j hj'))
          have h1 := indicator_value_mem_unit_interval hδ j
          have h2 := indicator_value_mem_unit_interval hδ' j
          unfold wordU
          nlinarith [mul_le_mul_of_nonneg_right h2.2 hΔ.le, mul_nonneg h1.1 hΔ.le]
      _ = (n : ℝ) / 3 := by
          rw [sum_const, card_range, nsmul_eq_mul, mul_one_div]
  have C := (abs_le.1 (g5w7_cloud_two n c hΔ hδ hδ')).2
  linarith
end Formalism.HermitianLattices.FormalDegreeBoundsAlt
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.FormalDegreeBoundsAlt
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.FormalDegreeBoundsAlt
theorem _root_.solution : VandermondeVariationExplicit := by
  intro k c Δ u0 uk δ δ' hk hΔ hδ hδ' hu0 halt
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have e2 : n + 2 - 2 = n := rfl
  rw [e2] at halt
  have ek : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have mono := g5w7_nlog_mono (show n ≤ n + 2 by omega)
  have nn := g5w7_nlog_nonneg n
  have lg : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  by_cases hz : u0 - uk = 0
  · rw [g5w7_colU_vand, g5w7_colU_vand, hz]
    simp only [mul_zero, zero_mul, Real.log_zero, sub_zero, abs_zero]
    linarith
  · rw [ek] at hu0 halt
    have hq : ∀ e : ℕ → ℕ, (∀ l, e l ≤ 1) → ∀ l, l < n → 3 * Δ ≤ wordU c Δ e l - uk := by
      intro e he l hl
      have h1 := indicator_value_mem_unit_interval he l
      have h2 := mul_le_mul_of_nonneg_right h1.2 hΔ.le
      rcases halt with rfl | h
      · have h3 := g5w7_gap hl
        have h4 := mul_le_mul_of_nonneg_left h3 hΔ.le
        unfold wordU cloudV
        nlinarith
      · have h3 := h l hl
        have h4 : 0 ≤ (n : ℝ) * Δ := by positivity
        unfold wordU
        nlinarith
    have a1 := g5w7_var_one n c u0 uk hΔ hδ hδ' hu0 hq hz
    have a2 := g5w7_var_one n c u0 uk hΔ hδ' hδ hu0 hq hz
    have hb : 7 / 12 * (n : ℝ) * (1 + Real.log n) + 1 / 4 + (n : ℝ) / 3 ≤
        ((n + 2 : ℕ) : ℝ) * (1 + Real.log ((n + 2 : ℕ) : ℝ)) + 2 := by
      have : (n : ℝ) / 3 ≤ 1 / 3 * ((n : ℝ) * (1 + Real.log n)) := by nlinarith
      linarith
    rw [abs_le]
    constructor <;> linarith
end Formalism.HermitianLattices.FormalDegreeBoundsAlt
