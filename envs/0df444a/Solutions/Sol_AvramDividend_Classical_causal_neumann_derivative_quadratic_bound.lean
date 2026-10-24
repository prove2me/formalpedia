-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_derivative_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:24:01.508674+00:00
-- url     : https://prove2.me/submissions/9a6e508c-65e0-42ba-8b79-1e3f546aee76

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Theorems.Thm_AvramDividend_Classical_causal_polynomial_geometric_derivative_series_C1
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.GroupWithZero.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- The quadratic-geometric pointwise power bounds imply a derivative
majorant for the exponentially weighted causal Neumann terms. -/
theorem solution
    (P H : ℕ → ℝ → ℝ) (a ε ρ w : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hρ : 0 ≤ ρ) (hw : 0 ≤ w)
    (hP : ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hH : ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a)
    (hDeriv : ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      deriv (H n) x = P n x / a - w * H n x) :
    ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |deriv (H n) x| ≤
        (1 / a) * (((n + 1 : ℝ) ^ 2 / ε) + w) * ρ ^ (n + 1) := by
  intro n x hx
  have hxpos : 0 < x := lt_of_lt_of_le hε hx
  have hnum : 0 ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) :=
    mul_nonneg (sq_nonneg _) (pow_nonneg hρ _)
  have hPε : |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / ε :=
    (hP n x hx).trans (div_le_div_of_nonneg_left hnum hε hx)
  have h1 := div_le_div_of_nonneg_right hPε ha.le
  have h2 := mul_le_mul_of_nonneg_left (hH n x hx) hw
  rw [hDeriv n x hx]
  calc
    |P n x / a - w * H n x| ≤ |P n x / a| + |w * H n x| :=
      by simpa using (abs_sub_le (P n x / a) 0 (w * H n x))
    _ = |P n x| / a + w * |H n x| := by
      rw [abs_div, abs_of_pos ha, abs_mul, abs_of_nonneg hw]
    _ ≤ (((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / ε) / a +
          w * (ρ ^ (n + 1) / a) := add_le_add h1 h2
    _ = (1 / a) * (((n + 1 : ℝ) ^ 2 / ε) + w) * ρ ^ (n + 1) := by ring
