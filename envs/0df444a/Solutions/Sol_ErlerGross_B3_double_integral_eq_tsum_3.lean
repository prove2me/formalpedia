-- Prove2me | solution 3 for ErlerGross.B3_double_integral_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T16:56:21.266906+00:00
-- url     : https://prove2.me/submissions/e22e08b8-729c-421a-b6cd-659e0a925bc0

import Mathlib
import Theorems.Thm_ErlerGross_B3_cubic_reciprocal_series_closed_form
open Real Filter Topology MeasureTheory Set

lemma b3_alt_geom_bound_intervalIntegrable :
    IntervalIntegrable (fun y : ℝ => ∑' n : ℕ, (1-y) * y^n) volume 0 1 := by
  have hEq : EqOn (fun y : ℝ => ∑' n : ℕ, (1-y) * y^n)
      (fun _ : ℝ => (1 : ℝ)) (Set.uIoo 0 1) := by
    intro y hy
    rw [uIoo_of_le (by norm_num)] at hy
    have hy0 : (0 : ℝ) ≤ y := le_of_lt hy.1
    have hy1 : y < 1 := hy.2
    have hnorm : ‖y‖ < (1 : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hy0]
      exact hy1
    have hgeom := hasSum_geometric_of_norm_lt_one hnorm
    have hscaled := hgeom.mul_left (1-y)
    have hyne : (1 - y : ℝ) ≠ 0 := by linarith
    simpa only [Pi.one_apply] using hscaled.tsum_eq.trans (by field_simp [hyne])
  rw [intervalIntegrable_congr_uIoo hEq]
  exact intervalIntegrable_const

lemma b3_alt_bound (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (n : ℕ) :
    ‖(1-y) * x^(2*n) * y^(3*n)‖ ≤ (1-y) * y^n := by
  have hx2 : x^2 ≤ (1 : ℝ) := pow_le_one₀ (by positivity) hx1
  have hy2 : y^2 ≤ (1 : ℝ) := pow_le_one₀ hy0 hy1
  have hxy : x^2 * y^2 ≤ (1 : ℝ) := mul_le_one₀ hx2 (by positivity) hy2
  have hbase : x^2 * y^3 ≤ y := by
    calc
      x^2 * y^3 = (x^2 * y^2) * y := by ring
      _ ≤ 1 * y := mul_le_mul_of_nonneg_right hxy hy0
      _ = y := by ring
  have hpow : (x^2 * y^3)^n ≤ y^n := pow_le_pow_left₀ (by positivity) hbase n
  have hprod : x^(2*n) * y^(3*n) = (x^2 * y^3)^n := by
    rw [pow_mul, pow_mul, ← mul_pow]
  have hprod' : x^(2*n) * y^(3*n) ≤ y^n := by rwa [hprod]
  have hleft : 0 ≤ (1-y) := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      (1-y) * x^(2*n) * y^(3*n) = (1-y) * (x^(2*n) * y^(3*n)) := by ring
      _ ≤ (1-y) * y^n := mul_le_mul_of_nonneg_left hprod' hleft
  · positivity

lemma b3_alt_rnorm (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hxy : x ≠ 1 ∨ y ≠ 1) : ‖x^2 * y^3‖ < (1 : ℝ) := by
  have hx2 : x^2 ≤ (1 : ℝ) := pow_le_one₀ (by positivity) hx1
  have hy3 : y^3 ≤ (1 : ℝ) := pow_le_one₀ hy0 hy1
  have hx2nonneg : 0 ≤ x^2 := by positivity
  have hy3nonneg : 0 ≤ y^3 := by positivity
  have hlt : x^2 * y^3 < (1 : ℝ) := by
    rcases hxy with hxne | hyne
    · have hxlt : x < 1 := lt_of_le_of_ne hx1 hxne
      have hx2lt : x^2 < (1 : ℝ) := pow_lt_one₀ hx0 hxlt (by norm_num)
      exact mul_lt_one_of_nonneg_of_lt_one_left hx2nonneg hx2lt hy3
    · by_cases hxeq : x = 1
      · subst x
        have hylt : y < 1 := lt_of_le_of_ne hy1 hyne
        have hy3lt : y^3 < (1 : ℝ) := pow_lt_one₀ hy0 hylt (by norm_num)
        simpa using mul_lt_one_of_nonneg_of_lt_one_right (by norm_num : (1:ℝ) ≤ 1)
          hy3nonneg hy3lt
      · have hxlt : x < 1 := lt_of_le_of_ne hx1 hxeq
        have hx2lt : x^2 < (1 : ℝ) := pow_lt_one₀ hx0 hxlt (by norm_num)
        exact mul_lt_one_of_nonneg_of_lt_one_left hx2nonneg hx2lt hy3
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hlt

lemma b3_alt_inner (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    HasSum (fun n : ℕ => ∫ y in (0 : ℝ)..1,
      (1-y) * x^(2*n) * y^(3*n))
      (∫ y in (0 : ℝ)..1, (1-y) / (1-x^2*y^3)) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n : ℕ => fun y : ℝ => (1-y) * y^n)
  · intro n
    fun_prop
  · intro n
    filter_upwards [] with y hy
    rw [uIoc_of_le (by norm_num)] at hy
    exact b3_alt_bound x y hx0 hx1 (le_of_lt hy.1) hy.2 n
  · filter_upwards [] with y hy
    rw [uIoc_of_le (by norm_num)] at hy
    have hy0 : (0 : ℝ) ≤ y := le_of_lt hy.1
    have hy1 : y ≤ 1 := hy.2
    by_cases hyeq : y = 1
    · simp [hyeq]
    · have hynorm : ‖y‖ < (1 : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hy0]
        exact lt_of_le_of_ne hy1 hyeq
      exact (hasSum_geometric_of_norm_lt_one hynorm).mul_left (1-y) |>.summable
  · exact b3_alt_geom_bound_intervalIntegrable
  · filter_upwards [] with y hy
    rw [uIoc_of_le (by norm_num)] at hy
    have hy0 : (0 : ℝ) ≤ y := le_of_lt hy.1
    have hy1 : y ≤ 1 := hy.2
    by_cases hcorner : x = 1 ∧ y = 1
    · simp [hcorner.1, hcorner.2]
    · have hxy : x ≠ 1 ∨ y ≠ 1 := by
        by_cases hxeq : x = 1
        · right
          intro hyeq
          exact hcorner ⟨hxeq, hyeq⟩
        · exact Or.inl hxeq
      have hrnorm : ‖x^2*y^3‖ < (1 : ℝ) := b3_alt_rnorm x y hx0 hx1 hy0 hy1 hxy
      have hgeom := hasSum_geometric_of_norm_lt_one hrnorm
      have hscaled := hgeom.mul_left (1-y)
      have hfun : HasSum (fun n : ℕ => (1-y) * x^(2*n) * y^(3*n))
          ((1-y) * (1-x^2*y^3)⁻¹) := by
        apply hscaled.congr_fun
        intro n
        rw [pow_mul, pow_mul]
        calc
          (1-y) * (x ^ 2) ^ n * (y ^ 3) ^ n =
              (1-y) * ((x ^ 2) ^ n * (y ^ 3) ^ n) := by ring
          _ = (1-y) * (x ^ 2 * y ^ 3) ^ n := by rw [mul_pow]
      simpa only [div_eq_mul_inv] using hfun

lemma b3_alt_finite_geom (y : ℝ) (N : ℕ) :
    (1-y) * (∑ n ∈ Finset.range N, y^n) = 1-y^N := by
  induction N with
  | zero => simp
  | succ N ih =>
    calc
      (1-y) * (∑ n ∈ Finset.range (N+1), y^n) =
          (1-y) * ((∑ n ∈ Finset.range N, y^n) + y^N) := by
            rw [Finset.sum_range_succ]
      _ = 1 - y^(N+1) := by rw [mul_add, ih]; ring

lemma b3_alt_inner_term (x : ℝ) (n : ℕ) :
    (∫ y in (0 : ℝ)..1, (1-y) * x^(2*n) * y^(3*n)) =
      x^(2*n) / ((3*n+1) * (3*n+2)) := by
  have h1 : IntervalIntegrable (fun y : ℝ => y^(3*n)) volume 0 1 := by
    exact (continuous_pow (3*n)).continuousOn.intervalIntegrable
  have h2 : IntervalIntegrable (fun y : ℝ => y^(3*n+1)) volume 0 1 := by
    exact (continuous_pow (3*n+1)).continuousOn.intervalIntegrable
  calc
    (∫ y in (0 : ℝ)..1, (1-y) * x^(2*n) * y^(3*n)) =
        ∫ y in (0 : ℝ)..1, x^(2*n) * (y^(3*n) - y^(3*n+1)) := by
          apply intervalIntegral.integral_congr
          intro y hy
          ring
    _ = x^(2*n) * (∫ y in (0 : ℝ)..1, y^(3*n) - y^(3*n+1)) := by
          rw [intervalIntegral.integral_const_mul]
    _ = x^(2*n) * ((∫ y in (0 : ℝ)..1, y^(3*n)) -
          ∫ y in (0 : ℝ)..1, y^(3*n+1)) := by
          rw [intervalIntegral.integral_sub h1 h2]
    _ = x^(2*n) / ((3*n+1) * (3*n+2)) := by
          rw [integral_pow, integral_pow]
          push_cast
          field_simp
          ring

lemma b3_alt_inner_sum_eq (x : ℝ) (N : ℕ) :
    (∫ y in (0 : ℝ)..1, ∑ n ∈ Finset.range N,
      (1-y) * x^(2*n) * y^(3*n)) =
      ∑ n ∈ Finset.range N, x^(2*n) / ((3*n+1) * (3*n+2)) := by
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    exact b3_alt_inner_term x n
  · intro n hn
    have hc : Continuous (fun y : ℝ => (1-y) * x^(2*n) * y^(3*n)) := by
      fun_prop
    exact hc.intervalIntegrable 0 1

lemma b3_alt_finite_bound (x : ℝ) (N : ℕ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (∑ n ∈ Finset.range N, x^(2*n) / ((3*n+1) * (3*n+2))) ∧
    (∑ n ∈ Finset.range N, x^(2*n) / ((3*n+1) * (3*n+2))) ≤ 1 := by
  have hFint : IntervalIntegrable
      (fun y : ℝ => ∑ n ∈ Finset.range N, (1-y) * x^(2*n) * y^(3*n)) volume 0 1 := by
    have hc : Continuous (fun y : ℝ =>
        ∑ n ∈ Finset.range N, (1-y) * x^(2*n) * y^(3*n)) := by
      apply continuous_finsetSum
      intro n hn
      fun_prop
    exact hc.intervalIntegrable 0 1
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 := intervalIntegrable_const
  have hnon : 0 ≤ ∫ y in (0 : ℝ)..1,
      ∑ n ∈ Finset.range N, (1-y) * x^(2*n) * y^(3*n) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro y hy
    apply Finset.sum_nonneg
    intro n hn
    have hy0 : (0 : ℝ) ≤ y := hy.1
    have hy1 : y ≤ 1 := hy.2
    positivity
  have hle : (∫ y in (0 : ℝ)..1,
      ∑ n ∈ Finset.range N, (1-y) * x^(2*n) * y^(3*n)) ≤
      ∫ y in (0 : ℝ)..1, (1 : ℝ) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hFint hconst
    intro y hy
    have hsum := Finset.sum_le_sum (s := Finset.range N) (fun n hn =>
      b3_alt_bound x y hx0 hx1 hy.1 hy.2 n)
    have hnonterms :
        (∑ n ∈ Finset.range N, (1-y) * x^(2*n) * y^(3*n)) =
          ∑ n ∈ Finset.range N, ‖(1-y) * x^(2*n) * y^(3*n)‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Real.norm_eq_abs, abs_of_nonneg]
      have hy0 : (0 : ℝ) ≤ y := hy.1
      have hy1 : y ≤ 1 := hy.2
      have h1 : (0 : ℝ) ≤ 1-y := by linarith
      positivity
    calc
      (∑ n ∈ Finset.range N, (1-y) * x^(2*n) * y^(3*n)) =
          ∑ n ∈ Finset.range N, ‖(1-y) * x^(2*n) * y^(3*n)‖ := hnonterms
      _ ≤ ∑ n ∈ Finset.range N, (1-y) * y^n := hsum
      _ = (1-y) * (∑ n ∈ Finset.range N, y^n) := by rw [Finset.mul_sum]
      _ = 1-y^N := b3_alt_finite_geom y N
      _ ≤ 1 := by nlinarith [pow_nonneg hy.1 N]
  rw [b3_alt_inner_sum_eq] at hnon hle
  constructor
  · exact hnon
  · simpa [intervalIntegral.integral_const] using hle

lemma b3_alt_outer_term (n : ℕ) :
    (∫ x in (0 : ℝ)..1, x^(2*n) / ((3*(n:ℝ)+1) * (3*(n:ℝ)+2))) =
      1 / ((2*(n:ℝ)+1) * (3*(n:ℝ)+1) * (3*(n:ℝ)+2)) := by
  calc
    (∫ x in (0 : ℝ)..1, x^(2*n) / ((3*(n:ℝ)+1) * (3*(n:ℝ)+2))) =
        ((3*(n:ℝ)+1) * (3*(n:ℝ)+2))⁻¹ * (∫ x in (0 : ℝ)..1, x^(2*n)) := by
          rw [show (fun x : ℝ => x^(2*n) / ((3*(n:ℝ)+1) * (3*(n:ℝ)+2))) =
              (fun x : ℝ => ((3*(n:ℝ)+1) * (3*(n:ℝ)+2))⁻¹ * x^(2*n)) by
                funext x; ring]
          rw [intervalIntegral.integral_const_mul]
    _ = 1 / ((2*(n:ℝ)+1) * (3*(n:ℝ)+1) * (3*(n:ℝ)+2)) := by
          rw [integral_pow]
          push_cast
          field_simp
          ring

lemma b3_alt_outer_sum_eq (N : ℕ) :
    (∫ x in (0 : ℝ)..1, ∑ n ∈ Finset.range N,
      x^(2*n) / ((3*(n:ℝ)+1) * (3*(n:ℝ)+2))) =
      ∑ n ∈ Finset.range N,
        1 / ((2*(n:ℝ)+1) * (3*(n:ℝ)+1) * (3*(n:ℝ)+2)) := by
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    exact b3_alt_outer_term n
  · intro n hn
    have hc : Continuous (fun x : ℝ => x^(2*n) /
        ((3*(n:ℝ)+1) * (3*(n:ℝ)+2))) := by
      fun_prop
    exact hc.intervalIntegrable 0 1

lemma b3_alt_outer_limit :
    Tendsto
      (fun N : ℕ => ∫ x in (0 : ℝ)..1, ∑ n ∈ Finset.range N,
        x^(2*n) / ((3*(n:ℝ)+1) * (3*(n:ℝ)+2)))
      atTop
      (𝓝 (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (1-y) / (1-x^2*y^3))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => (1 : ℝ))
  · filter_upwards [] with N
    have hc : Continuous (fun x : ℝ =>
        ∑ n ∈ Finset.range N,
          x^(2*n) / ((3*(n:ℝ)+1) * (3*(n:ℝ)+2))) := by
      apply continuous_finsetSum
      intro n hn
      fun_prop
    exact hc.aestronglyMeasurable.restrict
  · filter_upwards [] with N
    filter_upwards [] with x hx
    rw [uIoc_of_le (by norm_num)] at hx
    have hb := b3_alt_finite_bound x N (le_of_lt hx.1) hx.2
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  · exact intervalIntegrable_const
  · filter_upwards [] with x hx
    rw [uIoc_of_le (by norm_num)] at hx
    have hlim := (b3_alt_inner x (le_of_lt hx.1) hx.2).tendsto_sum_nat
    exact hlim.congr' (Filter.Eventually.of_forall (fun N => by
      apply Finset.sum_congr rfl
      intro n hn
      exact b3_alt_inner_term x n))


theorem solution :
    intervalIntegral (fun x : Real =>
      intervalIntegral (fun y : Real => (1 - y) / (1 - x ^ 2 * y ^ 3)) 0 1 volume) 0 1 volume =
      tsum (fun n : Nat => (1 : Real) / ((2 * n + 1) * (3 * n + 1) * (3 * n + 2))) := by
  have hout := b3_alt_outer_limit
  have hts : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        (1 : ℝ) / ((2*(n:ℝ)+1) * (3*(n:ℝ)+1) * (3*(n:ℝ)+2)))
      atTop (𝓝 (∑' n : ℕ, (1 : ℝ) /
        ((2*(n:ℝ)+1) * (3*(n:ℝ)+1) * (3*(n:ℝ)+2)))) := by
    exact (ErlerGross.B3_cubic_reciprocal_series_closed_form.summable.hasSum).tendsto_sum_nat
  have hout' : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        (1 : ℝ) / ((2*(n:ℝ)+1) * (3*(n:ℝ)+1) * (3*(n:ℝ)+2)))
      atTop (𝓝 (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (1-y) / (1-x^2*y^3))) := by
    exact hout.congr' (Filter.Eventually.of_forall (fun N => by
      exact b3_alt_outer_sum_eq N))
  exact (tendsto_nhds_unique hts hout').symm
