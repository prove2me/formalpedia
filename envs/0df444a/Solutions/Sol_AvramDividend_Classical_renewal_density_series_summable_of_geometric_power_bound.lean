-- Prove2me | solution 1 for AvramDividend.Classical.renewal_density_series_summable_of_geometric_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T08:12:21.871088+00:00
-- url     : https://prove2.me/submissions/d29cbe5c-df21-4bff-8859-5c0dc1365870

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A quadratic-geometric envelope makes each positive-time renewal series summable. -/
theorem solution
    (ρ x : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hx : 0 < x)
    (F : ℕ → ℝ) (hF0 : ∀ n : ℕ, 0 ≤ F n)
    (hFbound : ∀ n : ℕ,
      F n ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    Summable F := by
  have hnorm : ‖ρ‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hρ0] using hρ1
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ 2 * ρ ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hnorm
  have hs' : Summable (fun n : ℕ =>
      (n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) := by
    simpa only [Function.comp_def, Nat.cast_succ, Nat.succ_eq_add_one] using
      (hs.comp_injective Nat.succ_injective)
  have hs'' : Summable (fun n : ℕ =>
      ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :=
    hs'.div_const x
  apply Summable.of_norm_bounded hs''
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (hF0 n)]
  exact hFbound n
