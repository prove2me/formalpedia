-- Prove2me | solution 1 for AvramDividend.Classical.exp_compensated_near_zero_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:27:09.277395+00:00
-- url     : https://prove2.me/submissions/57467393-708a-44af-8401-287d5c1ca01f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∀ y ∈ Ioo (-r) 0,
        ‖Real.exp (θ * y) - 1 - θ * y‖ ≤ θ ^ 2 * y ^ 2 := by
  let r : ℝ := (1 + θ)⁻¹
  have hd : 0 < 1 + θ := by linarith
  have hr : 0 < r := by
    dsimp [r]
    exact inv_pos.mpr hd
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact (inv_le_one₀ hd).mpr (by linarith)
  refine ⟨r, hr, hr1, ?_⟩
  intro y hy
  have hy0 : y < 0 := hy.2
  have hyn : 0 ≤ -y := by linarith
  have hmul : θ * (-y) ≤ 1 := by
    have hθr : θ * r ≤ 1 := by
      dsimp [r]
      apply (mul_inv_le_iff₀ hd).mpr
      nlinarith
    have hyr : -r < y := hy.1
    have hry : 0 ≤ r + y := by linarith
    have hmulpos : 0 ≤ θ * (r + y) := mul_nonneg hθ hry
    nlinarith [hmulpos]
  have hnorm : ‖θ * y‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hθ hy0.le)]
    nlinarith
  have h := Real.norm_exp_sub_one_sub_id_le hnorm
  calc
    ‖Real.exp (θ * y) - 1 - θ * y‖ ≤ ‖θ * y‖ ^ 2 := h
    _ = θ ^ 2 * y ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
      ring
