-- Prove2me | solution 2 for ErlerGross.B3_double_integral_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T16:48:00.564729+00:00
-- url     : https://prove2.me/submissions/fd9c5b64-dd26-4cbf-b4ad-4422cd3e1974

import Mathlib
import Theorems.Thm_ErlerGross_B3_cubic_reciprocal_series_closed_form
open Real Filter Topology MeasureTheory

theorem subagent_eg_double_geom (x y : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    (∑' n : ℕ, (1-y) * x^(2*n) * y^(3*n)) = (1-y) / (1-x^2*y^3) := by
  let a : ℝ := x^2 * y^3
  have hx0 : 0 ≤ x := hx.1
  have hy0 : 0 ≤ y := hy.1
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have hx2 : x ^ 2 ≤ (1 : ℝ) := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ x + 1)
      (sub_nonpos.mpr hx.2)]
  have hy2 : y ^ 2 ≤ (1 : ℝ) := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ y + 1)
      (sub_nonpos.mpr hy.2)]
  have hy3 : y ^ 3 ≤ (1 : ℝ) := by
    calc
      y ^ 3 = y ^ 2 * y := by ring
      _ ≤ 1 * y := by exact mul_le_mul_of_nonneg_right hy2 hy0
      _ ≤ 1 * 1 := by exact mul_le_mul_of_nonneg_left hy.2 (by norm_num)
      _ = 1 := by norm_num
  have ha1 : a ≤ 1 := by
    dsimp [a]
    calc
      x ^ 2 * y ^ 3 ≤ 1 * y ^ 3 := mul_le_mul_of_nonneg_right hx2 (by positivity)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hy3 (by norm_num)
      _ = 1 := by norm_num
  by_cases hlt : a < 1
  · have hg := tsum_geometric_of_norm_lt_one (ξ := a) (by
      rw [Real.norm_of_nonneg ha0]
      exact hlt)
    have hga : (∑' n : ℕ, (1-y) * a^n) = (1-y) / (1-a) := by
      rw [tsum_mul_left]
      simpa [div_eq_mul_inv] using congrArg (fun z : ℝ => (1-y) * z) hg
    have hpow : ∀ n : ℕ, (1-y) * a^n = (1-y) * x^(2*n) * y^(3*n) := by
      intro n
      dsimp [a]
      rw [mul_pow, ← pow_mul, ← pow_mul]
      ring
    calc
      ∑' n : ℕ, (1-y) * x^(2*n) * y^(3*n) = ∑' n : ℕ, (1-y) * a^n := by
        apply tsum_congr
        intro n
        exact (hpow n).symm
      _ = (1-y) / (1-a) := hga
      _ = (1-y) / (1-x^2*y^3) := by rfl
  · have haeq : a = 1 := le_antisymm ha1 (le_of_not_gt hlt)
    have hmul : x ^ 2 * y ^ 3 ≤ y ^ 3 := by
      calc
        x ^ 2 * y ^ 3 ≤ 1 * y ^ 3 := mul_le_mul_of_nonneg_right hx2 (by positivity)
        _ = y ^ 3 := by ring
    have hy3eq : y ^ 3 = 1 := by
      apply le_antisymm hy3
      rw [← haeq]
      exact hmul
    have hyeq : y = 1 := by
      exact (pow_eq_one_iff_of_nonneg hy0 (by norm_num)).mp hy3eq
    simp [hyeq]


theorem subagent_eg_inner_sum (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    (∫ y in (0 : ℝ)..1, (1-y) / (1-x^2*y^3)) =
      ∑' n : ℕ, x^(2*n) / ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2)) := by
  have hmajor : Summable (fun n : ℕ => 1 / ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))) := by
    have hpabs := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
    have hp : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      apply hpabs.congr
      intro n
      rw [abs_of_nonneg]
      · congr 1
        norm_num [pow_two]
      · positivity
    apply hp.of_nonneg_of_le
    · intro n
      positivity
    · intro n
      have hbase : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
      apply one_div_le_one_div_of_le hbase
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hFint : ∀ n : ℕ,
      Integrable (fun y : ℝ => (1-y) * x^(2*n) * y^(3*n))
        (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    intro n
    have hc : Continuous (fun y : ℝ => (1-y) * x^(2*n) * y^(3*n)) := by fun_prop
    have hioc : IntegrableOn (fun y : ℝ => (1-y) * x^(2*n) * y^(3*n))
        (Set.Ioc (0:ℝ) 1) :=
      (hc.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    exact hioc.integrable
  have hnorm : ∀ n : ℕ,
      (∫ y, ‖(1-y) * x^(2*n) * y^(3*n)‖
        ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) =
        x ^ (2*n) / ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2)) := by
    intro n
    have hnonneg : Set.EqOn (fun y : ℝ => ‖(1-y) * x^(2*n) * y^(3*n)‖)
        (fun y : ℝ => (1-y) * x^(2*n) * y^(3*n)) (Set.Ioc 0 1) := by
      intro y hy
      dsimp
      rw [abs_of_nonneg]
      have hy0 : 0 ≤ y := hy.1.le
      have hy1 : y ≤ 1 := hy.2
      exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hy1) (pow_nonneg hx.1 _))
        (pow_nonneg hy0 _)
    rw [MeasureTheory.integral_congr_ae]
    · rw [← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
      have heq : (fun y : ℝ => (1-y) * x^(2*n) * y^(3*n)) =
          (fun y : ℝ => x^(2*n) * (y^(3*n) - y^(3*n+1))) := by
        funext y
        ring
      rw [heq, intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_sub (continuous_pow _ |>.intervalIntegrable 0 1)
        (continuous_pow _ |>.intervalIntegrable 0 1)]
      rw [integral_pow, integral_pow]
      norm_num
      have h1 : (0 : ℝ) < 3 * (n : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < 3 * (n : ℝ) + 2 := by positivity
      field_simp [ne_of_gt h1, ne_of_gt h2]
      ring
    · exact ae_restrict_of_forall_mem measurableSet_Ioc hnonneg
  have hFsum : Summable (fun n : ℕ =>
      ∫ y, ‖(1-y) * x^(2*n) * y^(3*n)‖
        ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    apply hmajor.of_nonneg_of_le
    · intro n
      positivity
    · intro n
      rw [hnorm n]
      apply div_le_div_of_nonneg_right (pow_le_one₀ hx.1 hx.2)
      positivity
  have hswap := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (0:ℝ) 1)) (F := fun n : ℕ =>
      fun y : ℝ => (1-y) * x^(2*n) * y^(3*n)) hFint hFsum
  have hswap' := hswap
  simp_rw [← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)] at hswap'
  have hsum_fun : Set.EqOn (fun y : ℝ =>
      ∑' n : ℕ, (1-y) * x^(2*n) * y^(3*n))
      (fun y : ℝ => (1-y) / (1-x^2*y^3)) (Set.uIcc 0 1) := by
    intro y hy
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le] using hy
    exact subagent_eg_double_geom x y hx hy'
  rw [intervalIntegral.integral_congr hsum_fun] at hswap'
  have hinner (n : ℕ) :
      (∫ y in (0 : ℝ)..1, (1-y) * x^(2*n) * y^(3*n)) =
        x^(2*n) / ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2)) := by
    have heq : (fun y : ℝ => (1-y) * x^(2*n) * y^(3*n)) =
        (fun y : ℝ => x^(2*n) * (y^(3*n) - y^(3*n+1))) := by
      funext y
      ring
    rw [heq, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub (continuous_pow _ |>.intervalIntegrable 0 1)
      (continuous_pow _ |>.intervalIntegrable 0 1)]
    rw [integral_pow, integral_pow]
    norm_num
    have h1 : (0 : ℝ) < 3 * (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < 3 * (n : ℝ) + 2 := by positivity
    field_simp [ne_of_gt h1, ne_of_gt h2]
    ring
  simp_rw [hinner] at hswap'
  exact hswap'.symm


theorem solution :
    intervalIntegral (fun x : Real =>
      intervalIntegral (fun y : Real => (1 - y) / (1 - x ^ 2 * y ^ 3)) 0 1 volume) 0 1 volume =
      tsum (fun n : Nat => (1 : Real) / ((2 * n + 1) * (3 * n + 1) * (3 * n + 2))) := by
  have hgs : Summable (fun n : ℕ =>
      1 / (((2 * (n : ℝ) + 1) * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2)))) :=
    ErlerGross.B3_cubic_reciprocal_series_closed_form.summable
  have hGint : ∀ n : ℕ,
      Integrable (fun x : ℝ => x^(2*n) /
        ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2)))
        (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    intro n
    have hc : Continuous (fun x : ℝ => x^(2*n) /
        ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))) := by fun_prop
    have hioc : IntegrableOn (fun x : ℝ => x^(2*n) /
        ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2)))
        (Set.Ioc (0:ℝ) 1) :=
      (hc.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    exact hioc.integrable
  have hGnorm : ∀ n : ℕ,
      (∫ x, ‖x^(2*n) /
        ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))‖
        ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) =
      1 / (((2 * (n : ℝ) + 1) * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))) := by
    intro n
    have hnonneg : Set.EqOn
        (fun x : ℝ => ‖x^(2*n) /
          ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))‖)
        (fun x : ℝ => x^(2*n) /
          ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))) (Set.Ioc 0 1) := by
      intro x hx
      dsimp
      rw [abs_of_nonneg]
      have hx0 : 0 ≤ x := hx.1.le
      positivity
    rw [MeasureTheory.integral_congr_ae]
    · rw [← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
      have heq : (fun x : ℝ => x^(2*n) /
          ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))) =
          (fun x : ℝ => ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))⁻¹ * x^(2*n)) := by
        funext x
        ring
      rw [heq, intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      have h1 : (0 : ℝ) < 3 * (n : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < 3 * (n : ℝ) + 2 := by positivity
      have h3 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
      field_simp [ne_of_gt h1, ne_of_gt h2, ne_of_gt h3]
    · exact ae_restrict_of_forall_mem measurableSet_Ioc hnonneg
  have hGsum : Summable (fun n : ℕ =>
      ∫ x, ‖x^(2*n) /
        ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))‖
        ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    exact hgs.congr (fun n => (hGnorm n).symm)
  have hswap := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (0:ℝ) 1)) (F := fun n : ℕ =>
      fun x : ℝ => x^(2*n) /
        ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))) hGint hGsum
  have hswap' := hswap
  simp_rw [← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)] at hswap'
  have hsum_fun : Set.EqOn (fun x : ℝ =>
      ∑' n : ℕ, x^(2*n) /
        ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2)))
      (fun x : ℝ => ∫ y in (0 : ℝ)..1, (1-y) / (1-x^2*y^3))
      (Set.uIcc 0 1) := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le] using hx
    exact (subagent_eg_inner_sum x hx').symm
  rw [intervalIntegral.integral_congr hsum_fun] at hswap'
  have houter (n : ℕ) :
      (∫ x in (0 : ℝ)..1, x^(2*n) /
        ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))) =
      1 / (((2 * (n : ℝ) + 1) * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))) := by
    have heq : (fun x : ℝ => x^(2*n) /
        ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))) =
        (fun x : ℝ => ((3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))⁻¹ * x^(2*n)) := by
      funext x
      ring
    rw [heq, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    have h1 : (0 : ℝ) < 3 * (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < 3 * (n : ℝ) + 2 := by positivity
    have h3 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
    field_simp [ne_of_gt h1, ne_of_gt h2, ne_of_gt h3]
  simp_rw [houter] at hswap'
  exact hswap'.symm
