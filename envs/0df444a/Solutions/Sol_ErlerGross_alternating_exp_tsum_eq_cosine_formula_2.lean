-- Prove2me | solution 2 for ErlerGross.alternating_exp_tsum_eq_cosine_formula
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:49:09.09176+00:00
-- url     : https://prove2.me/submissions/63f7c716-ee59-4a78-a661-9c13df4ae7ca

import Mathlib
import Definitions.Def_ErlerGross_defs

open Real Filter Topology MeasureTheory

theorem eg1ff_term_norm (n : ℕ) :
    ‖(-1 : ℂ)^n *
      (1 / (((2 * n + 1 : ℕ) : ℂ) * 1 - 0) + 1 / (((2 * n + 1 : ℕ) : ℂ) * 1 + 0))‖
      = 2 / (2 * (n : ℝ) + 1) := by
  have hx : (((2 * n + 1 : ℕ) : ℂ) * 1 - 0) = (((2 * (n : ℝ) + 1 : ℝ)) : ℂ) := by
    push_cast; ring
  have hy : (((2 * n + 1 : ℕ) : ℂ) * 1 + 0) = (((2 * (n : ℝ) + 1 : ℝ)) : ℂ) := by
    push_cast; ring
  rw [hx, hy, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hpos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  rw [show (1 / ((2 * (n : ℝ) + 1 : ℝ) : ℂ) + 1 / ((2 * (n : ℝ) + 1 : ℝ) : ℂ))
      = (((2 / (2 * (n : ℝ) + 1)) : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem eg1ff_not_summable :
    ¬ Summable (fun n : ℕ => (-1 : ℂ)^n *
      (1 / (((2 * n + 1 : ℕ) : ℂ) * 1 - 0) + 1 / (((2 * n + 1 : ℕ) : ℂ) * 1 + 0))) := by
  intro h
  have h2 := h.norm
  simp only [eg1ff_term_norm] at h2
  have h3 : Summable (fun n : ℕ => 1 / ((↑(n + 1) : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h2
    have hpos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
    push_cast
    rw [div_le_div_iff₀ (by positivity) hpos]
    linarith
  have h4 : Summable (fun n : ℕ => 1 / (n : ℝ)) :=
    (summable_nat_add_iff 1).mp h3
  exact Real.not_summable_one_div_natCast h4

theorem solution : ¬ (∀ (a b : ℂ), |a.re| < b.re →
    ∑' n : ℕ, (-1 : ℂ)^n *
      (1 / (((2 * n + 1 : ℕ) : ℂ) * b - a) +
       1 / (((2 * n + 1 : ℕ) : ℂ) * b + a)) =
      (π : ℂ) / (2 * b) * (1 / Complex.cos (π * a / (2 * b)))) := by
  intro H
  have h := H 0 1 (by simp)
  rw [tsum_eq_zero_of_not_summable eg1ff_not_summable] at h
  simp only [mul_zero, zero_div, Complex.cos_zero, div_one, mul_one] at h
  have hpi : (π : ℂ) / 2 ≠ 0 := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact div_ne_zero this two_ne_zero
  exact hpi h.symm

