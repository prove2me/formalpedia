-- Prove2me | solution 2 for ErlerGross.alternating_exp_hasSum_cosine_formula
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:46:30.643096+00:00
-- url     : https://prove2.me/submissions/46076ae5-d296-41f3-b6a0-f1f9accbddc2

import Mathlib
import Definitions.Def_ErlerGross_defs

/-! Disproof of cc1e5374 `ErlerGross.alternating_exp_hasSum_cosine_formula`.

`HasSum` in `ℂ` is unconditional summation, which in a finite-dimensional space is absolute
summation. The terms are `(-1)^n * 2(2n+1)b / ((2n+1)^2 b^2 - a^2)`, of norm `~ 1/(n |b|)`,
so the series is only conditionally convergent. Concretely at `a = 0`, `b = 1` the norms are
`2/(2n+1) ≥ 1/(n+1)`, and the harmonic series diverges. -/

set_option autoImplicit false

theorem eg_cc1e_norm (n : ℕ) :
    ‖(-1 : Complex)^n *
      (1 / (((2 * n + 1 : Nat) : Complex) * 1 - 0) +
       1 / (((2 * n + 1 : Nat) : Complex) * 1 + 0))‖ = 2 / (2 * (n : ℝ) + 1) := by
  have h : (1 / (((2 * n + 1 : Nat) : Complex) * 1 - 0) +
       1 / (((2 * n + 1 : Nat) : Complex) * 1 + 0)) = (((2 / (2 * (n : ℝ) + 1)) : ℝ) : Complex) := by
    simp only [mul_one, sub_zero, add_zero]
    rw [← add_div, one_add_one_eq_two]
    push_cast
    rfl
  rw [h, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem eg_cc1e_not_summable :
    ¬ Summable (fun n : Nat => (-1 : Complex)^n *
      (1 / (((2 * n + 1 : Nat) : Complex) * 1 - 0) +
       1 / (((2 * n + 1 : Nat) : Complex) * 1 + 0))) := by
  intro hs
  have hn := (summable_norm_iff (E := Complex)).mpr hs
  simp only [eg_cc1e_norm] at hn
  have h1 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hn
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp h1)

open Real Filter Topology MeasureTheory in
theorem solution : ¬ (∀ (a b : Complex), |a.re| < b.re →
    HasSum (fun n : Nat => (-1 : Complex)^n *
      (1 / (((2 * n + 1 : Nat) : Complex) * b - a) +
       1 / (((2 * n + 1 : Nat) : Complex) * b + a)))
      ((Real.pi : Complex) / (2 * b) * (1 / Complex.cos ((Real.pi : Complex) * a / (2 * b))))) := by
  intro H
  exact eg_cc1e_not_summable (H 0 1 (by simp)).summable

