-- Prove2me | solution 2 for ErlerGross.alternating_exp_hasSum_cosh_integral
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:55:35.212451+00:00
-- url     : https://prove2.me/submissions/efb77e6f-c0f6-45d0-a955-2eca958b5674

import Mathlib

namespace ErlerGrossCexE9

theorem norm_term (n : ℕ) :
    ‖(-1 : ℂ)^n * (1 / (((2 * n + 1 : ℕ) : ℂ) * 1 - 0) +
       1 / (((2 * n + 1 : ℕ) : ℂ) * 1 + 0))‖ = 2 / (2 * (n : ℝ) + 1) := by
  have hpos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have h : (1 / (((2 * n + 1 : ℕ) : ℂ) * 1 - 0) + 1 / (((2 * n + 1 : ℕ) : ℂ) * 1 + 0))
      = ((2 / (2 * (n : ℝ) + 1) : ℝ) : ℂ) := by
    simp only [mul_one, sub_zero, add_zero]
    push_cast
    rw [← add_div]
    norm_num
  rw [h, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem not_summable_cex :
    ¬ Summable (fun n : ℕ => (-1 : ℂ)^n *
      (1 / (((2 * n + 1 : ℕ) : ℂ) * 1 - 0) +
       1 / (((2 * n + 1 : ℕ) : ℂ) * 1 + 0))) := by
  intro hs
  have h1 := summable_norm_iff.mpr hs
  simp only [norm_term] at h1
  have h2 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h1
    have hpos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
    rw [div_le_div_iff₀ (by positivity) hpos]
    linarith
  have h3 : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    rw [← summable_nat_add_iff 1]
    simpa [Nat.cast_add, Nat.cast_one] using h2
  exact Real.not_summable_one_div_natCast h3

end ErlerGrossCexE9

open Real Filter Topology MeasureTheory in
theorem solution : ¬ (∀ (a b : ℂ), |a.re| < b.re →
    HasSum (fun n : ℕ => (-1 : ℂ)^n *
      (1 / (((2 * n + 1 : ℕ) : ℂ) * b - a) +
       1 / (((2 * n + 1 : ℕ) : ℂ) * b + a)))
      (∫ t in Set.Ioi (0 : ℝ),
        Complex.cosh (a * (t : ℂ)) / Complex.cosh (b * (t : ℂ)))) := by
  intro h
  exact ErlerGrossCexE9.not_summable_cex (h 0 1 (by simp)).summable
