-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_gaussian_neumann_termwise_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:03:51.475188+00:00
-- url     : https://prove2.me/submissions/0d6c62cf-f3c9-412e-91e1-1ac48448e32b

import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_neumann_derivative_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_causal_polynomial_geometric_majorant_conversion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set

/-- The signed Gaussian Neumann primitive series has its exact termwise derivative. -/
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
    (y₀ : ℝ) (hy₀ : y₀ ∈ Ioo ε R)
    (hval : Summable (fun n : ℕ => H n y₀))
    (y : ℝ) (hy : y ∈ Ioo ε R) :
    HasDerivAt (fun z : ℝ => ∑' n : ℕ, H n z)
      (∑' n : ℕ, (P n y / a - w * H n y)) y := by
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
  have hbound : ∀ n : ℕ, ∀ z : ℝ, z ∈ Ioo ε R →
      ‖P n z / a - w * H n z‖ ≤
        (2 * A + B) * (((n : ℝ) ^ 2 + 1) * ρ ^ n) := by
    intro n z hz
    have hcoef : (1 / a) * (((n + 1 : ℝ) ^ 2 / ε) + w) =
        A * (n + 1 : ℝ) ^ 2 + B := by
      dsimp [A, B]
      ring
    have hbound0 := causal_neumann_derivative_quadratic_bound
      P H a ε ρ w ha hε hρ0 hw hP hH hderiv n z hz.1.le
    have hbound1 := causal_polynomial_geometric_majorant_conversion
      n A B ρ hA hB hρ0 hρ1.le
    have heq : ‖P n z / a - w * H n z‖ = |deriv (H n) z| := by
      rw [hderiv n z hz.1.le, Real.norm_eq_abs]
    calc
      ‖P n z / a - w * H n z‖ = |deriv (H n) z| := heq
      _ ≤ (1 / a) * (((n + 1 : ℝ) ^ 2 / ε) + w) *
          ρ ^ (n + 1) := hbound0
      _ = (A * (n + 1 : ℝ) ^ 2 + B) * ρ ^ (n + 1) := by rw [hcoef]
      _ ≤ (2 * A + B) * ((n : ℝ) ^ 2 + 1) * ρ ^ n := hbound1
      _ = (2 * A + B) * (((n : ℝ) ^ 2 + 1) * ρ ^ n) := by ring
  have hρnorm : ‖ρ‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hρ0] using hρ1
  have hpoly : Summable (fun n : ℕ => (n : ℝ) ^ 2 * ρ ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hρnorm
  have hgeom : Summable (fun n : ℕ => ρ ^ n) :=
    summable_geometric_of_norm_lt_one hρnorm
  have hu : Summable (fun n : ℕ =>
      (2 * A + B) * (((n : ℝ) ^ 2 + 1) * ρ ^ n)) := by
    have hsum : Summable (fun n : ℕ =>
        (2 * A + B) * ((n : ℝ) ^ 2 * ρ ^ n + ρ ^ n)) :=
      (hpoly.add hgeom).mul_left (2 * A + B)
    simpa only [add_mul, one_mul] using hsum
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    isPreconnected_Ioo
    (fun n z hz => hHasDeriv n z hz.1.le)
    hbound hy₀ hval hy
