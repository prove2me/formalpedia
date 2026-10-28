-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_series_C1_of_signed_power_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:23:46.577714+00:00
-- url     : https://prove2.me/submissions/2cd6a6ca-d8e4-4d81-8d3c-373f36b6b1ee

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_neumann_derivative_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_causal_polynomial_geometric_majorant_conversion
import Theorems.Thm_AvramDividend_Classical_causal_polynomial_geometric_derivative_series_C1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set

/-- Bounds from antitone envelope convolution powers imply C1 of the
signed damped Neumann series on every positive-time compact interval. -/
theorem solution
    (P H : ℕ → ℝ → ℝ) (a ε R ρ w : ℝ)
    (ha : 0 < a) (hε : 0 < ε)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hP : ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hH : ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a)
    (hHasDeriv : ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      HasDerivAt (H n) (P n x / a - w * H n x) x)
    (hCont : ∀ n : ℕ,
      ContinuousOn (fun x : ℝ => P n x / a - w * H n x) (Ioo ε R))
    (y₀ : ℝ) (hy₀ : y₀ ∈ Ioo ε R)
    (hval : Summable fun n : ℕ => H n y₀) :
    ContDiffOn ℝ 1 (fun y : ℝ => ∑' n : ℕ, H n y) (Ioo ε R) := by
  let A : ℝ := (1 / a) / ε
  let B : ℝ := (1 / a) * w
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (div_nonneg zero_le_one ha.le) hε.le
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (div_nonneg zero_le_one ha.le) hw
  have hderiv : ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      deriv (H n) x = P n x / a - w * H n x := by
    intro n x hx
    exact (hHasDeriv n x hx).deriv
  have hbound : ∀ n : ℕ, ∀ y : ℝ, y ∈ Ioo ε R →
      ‖P n y / a - w * H n y‖ ≤
        (2 * A + B) * (((n : ℝ) ^ 2 + 1) * ρ ^ n) := by
    intro n y hy
    have hcoef : (1 / a) * (((n + 1 : ℝ) ^ 2 / ε) + w) =
        A * (n + 1 : ℝ) ^ 2 + B := by
      dsimp [A, B]
      ring
    have hbound0 := causal_neumann_derivative_quadratic_bound
      P H a ε ρ w ha hε hρ0 hw hP hH hderiv n y hy.1.le
    have hbound1 := causal_polynomial_geometric_majorant_conversion
      n A B ρ hA hB hρ0 hρ1.le
    have heq : ‖P n y / a - w * H n y‖ = |deriv (H n) y| := by
      rw [hderiv n y hy.1.le, Real.norm_eq_abs]
    calc
      ‖P n y / a - w * H n y‖ = |deriv (H n) y| := heq
      _ ≤ (1 / a) * (((n + 1 : ℝ) ^ 2 / ε) + w) * ρ ^ (n + 1) := hbound0
      _ = (A * (n + 1 : ℝ) ^ 2 + B) * ρ ^ (n + 1) := by rw [hcoef]
      _ ≤ (2 * A + B) * ((n : ℝ) ^ 2 + 1) * ρ ^ n := hbound1
      _ = (2 * A + B) * (((n : ℝ) ^ 2 + 1) * ρ ^ n) := by ring
  exact causal_polynomial_geometric_derivative_series_C1
    H (fun n x => P n x / a - w * H n x)
    ε R (2 * A + B) ρ hρ0 hρ1
    (by
      intro n y hy
      exact hHasDeriv n y hy.1.le)
    hCont hbound y₀ hy₀ hval
