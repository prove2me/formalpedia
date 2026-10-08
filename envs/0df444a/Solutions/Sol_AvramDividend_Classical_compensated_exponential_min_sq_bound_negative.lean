-- Prove2me | solution 1 for AvramDividend.Classical.compensated_exponential_min_sq_bound_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:35:08.561304+00:00
-- url     : https://prove2.me/submissions/659f3ce0-6063-4d8f-bd37-d7fac6de239d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_compensated_exponential_quadratic_of_small_argument
import Theorems.Thm_AvramDividend_Classical_negative_exponential_increment_norm_le_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y < 0,
      ‖Real.exp (θ * y) - 1 -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator
          (fun _ : ℝ => (1 : ℝ)) y)‖ ≤ C * min 1 (y ^ 2) := by
  let r : ℝ := 1 / (θ + 1)
  have hplus : 0 < θ + 1 := by linarith
  have hr : 0 < r := by dsimp [r]; positivity
  have hrle : r ≤ 1 := by
    dsimp [r]
    apply (div_le_iff₀ hplus).2
    linarith
  have hmul : (θ + 1) * r = 1 := by
    dsimp [r]
    field_simp
  have hθr : θ * r ≤ 1 := by nlinarith [hmul, hr]
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  let C : ℝ := max (θ ^ 2) ((1 + θ) / (r ^ 2))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact (sq_nonneg θ).trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro y hy
  by_cases hnear : -r < y
  · have hyabs : |y| < r := by
      rw [abs_of_neg hy]
      linarith
    have hsmall : ‖θ * y‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hθ]
      exact (mul_le_mul_of_nonneg_left hyabs.le hθ).trans hθr
    have hyI : y ∈ Ioo (-1 : ℝ) 1 := by
      exact ⟨by linarith [hnear, hrle], by linarith⟩
    have hpos : 0 < (1 + y) * (1 - y) :=
      mul_pos (by linarith [hyI.1]) (by linarith [hyI.2])
    have hy2 : y ^ 2 ≤ 1 := by nlinarith
    have hmin : min (1 : ℝ) (y ^ 2) = y ^ 2 := min_eq_right hy2
    have hbound := compensated_exponential_quadratic_of_small_argument
      θ y hsmall
    have hind : (Ioo (-1 : ℝ) 1).indicator
        (fun _ : ℝ => (1 : ℝ)) y = 1 := by
      simp [Set.indicator_of_mem hyI]
    rw [hind, mul_one, hmin]
    exact hbound.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg y))
  · have hyr : y ≤ -r := le_of_not_gt hnear
    have hexp : ‖Real.exp (θ * y) - 1‖ ≤ (1 : ℝ) :=
      negative_exponential_increment_norm_le_one θ y hθ hy.le
    have htrunc : ‖θ * (y * (Ioo (-1 : ℝ) 1).indicator
        (fun _ : ℝ => (1 : ℝ)) y)‖ ≤ θ := by
      by_cases hyI : y ∈ Ioo (-1 : ℝ) 1
      · have hind : (Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y = 1 := by
          simp [Set.indicator_of_mem hyI]
        rw [hind, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hθ]
        have hyabs : |y| ≤ 1 := (abs_lt.2 hyI).le
        nlinarith
      · have hind : (Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y = 0 := by
          simp [Set.indicator, hyI]
        simp [hind, hθ]
    have hfar : ‖Real.exp (θ * y) - 1 -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator
          (fun _ : ℝ => (1 : ℝ)) y)‖ ≤ 1 + θ := by
      exact (norm_sub_le _ _).trans (add_le_add hexp htrunc)
    have hry : r ≤ -y := by linarith
    have hsq : r ^ 2 ≤ y ^ 2 := by nlinarith
    have hr2le : r ^ 2 ≤ 1 := by nlinarith [hr, hrle]
    have hmin : r ^ 2 ≤ min (1 : ℝ) (y ^ 2) := le_min hr2le hsq
    have hcoef : 1 + θ ≤ C * r ^ 2 := by
      have hc0 : (1 + θ) / (r ^ 2) ≤ C := le_max_right _ _
      exact (div_le_iff₀ hr2).mp hc0
    calc
      ‖Real.exp (θ * y) - 1 -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator
          (fun _ : ℝ => (1 : ℝ)) y)‖ ≤ 1 + θ := hfar
      _ ≤ C * r ^ 2 := hcoef
      _ ≤ C * min 1 (y ^ 2) :=
        mul_le_mul_of_nonneg_left hmin hC
