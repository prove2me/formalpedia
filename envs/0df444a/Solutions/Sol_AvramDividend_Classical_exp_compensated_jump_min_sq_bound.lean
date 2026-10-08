-- Prove2me | solution 1 for AvramDividend.Classical.exp_compensated_jump_min_sq_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:32:15.016625+00:00
-- url     : https://prove2.me/submissions/1c2f7051-589a-410b-9222-d37fcec794fc

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exp_negative_quadratic_remainder

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y < 0,
        ‖Real.exp (θ * y) - 1 -
          θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y‖ ≤
          C * min 1 (y ^ 2) := by
  let C : ℝ := max 1 (θ ^ 2)
  have hC : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro y hy
  have hθy : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ hy.le
  by_cases hfar : y ≤ -1
  · have hnot : y ∉ Ioo (-1 : ℝ) 1 := by
      simp only [mem_Ioo, not_and]
      intro h
      linarith
    have hmin : min (1 : ℝ) (y ^ 2) = 1 :=
      min_eq_left (by nlinarith)
    have he1 : Real.exp (θ * y) ≤ 1 :=
      (Real.exp_monotone hθy).trans (by norm_num)
    have he0 : 0 ≤ Real.exp (θ * y) := (Real.exp_pos _).le
    have hbound : ‖Real.exp (θ * y) - 1‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      linarith
    have hnorm :
        ‖Real.exp (θ * y) - 1 -
          θ * y * (Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y‖ ≤ 1 := by
      simpa [Set.indicator, hnot] using hbound
    rw [hmin]
    exact hnorm.trans (by simpa [C] using
      (le_max_left (1 : ℝ) (θ ^ 2)))
  · have hmem : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hmin : min (1 : ℝ) (y ^ 2) = y ^ 2 :=
      min_eq_right (by nlinarith)
    have hnorm :
        ‖Real.exp (θ * y) - 1 -
          θ * y * (Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y‖ =
        ‖Real.exp (θ * y) - 1 - θ * y‖ := by
      simp [Set.indicator, hmem]
    rw [hmin, hnorm]
    calc
      ‖Real.exp (θ * y) - 1 - θ * y‖ ≤ (θ * y) ^ 2 :=
        exp_negative_quadratic_remainder (θ * y) hθy
      _ = θ ^ 2 * y ^ 2 := by ring
      _ ≤ C * y ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right 1 (θ ^ 2)) (sq_nonneg y)
