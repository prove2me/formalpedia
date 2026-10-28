-- Prove2me | solution 1 for AvramDividend.Classical.causal_gaussian_primitive_local_geometric
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T21:26:48.842753+00:00
-- url     : https://prove2.me/submissions/1e1b96a9-0625-419d-91d2-0953db147eca

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real Set

/-- Damped primitive bounds give geometric estimates for undamped Gaussian corrections on each interval. -/
theorem solution
    (H Q : ℕ → ℝ → ℝ) (a w ρ : ℝ)
    (ha : 0 < a) (hw : 0 ≤ w) (hρ0 : 0 ≤ ρ)
    (hQ0 : Q 0 = fun _ : ℝ => 1 / a)
    (hQstep : ∀ n : ℕ, Q (n + 1) =
      fun s : ℝ => Real.exp (w * s) * H n s)
    (hHbound : ∀ n : ℕ, ∀ s : ℝ, 0 ≤ s →
      ‖H n s‖ ≤ ρ ^ (n + 1) / a) :
    ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ s ∈ Ioc (0 : ℝ) x,
        ‖Q n s‖ ≤ C * ρ ^ n := by
  intro x
  have ha1 : 0 < (1 / a : ℝ) := div_pos zero_lt_one ha
  refine ⟨max (1 / a) (Real.exp (w * x) / a),
    (le_of_lt ha1).trans (le_max_left _ _), ?_⟩
  intro n s hs
  cases n with
  | zero =>
      have hz : Q 0 s = 1 / a := by rw [hQ0]
      rw [hz, Real.norm_eq_abs, abs_of_pos ha1, pow_zero, mul_one]
      exact le_max_left _ _
  | succ n =>
      have hws : w * s ≤ w * x := mul_le_mul_of_nonneg_left hs.2 hw
      have hex : Real.exp (w * s) ≤ Real.exp (w * x) := Real.exp_le_exp.mpr hws
      have hE : Real.exp (w * s) / a ≤
          max (1 / a) (Real.exp (w * x) / a) :=
        (div_le_div_of_nonneg_right hex (le_of_lt ha)).trans (le_max_right _ _)
      calc
        ‖Q (n + 1) s‖ = Real.exp (w * s) * ‖H n s‖ := by
          rw [hQstep n]
          simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp (w * s) * (ρ ^ (n + 1) / a) :=
          mul_le_mul_of_nonneg_left (hHbound n s (le_of_lt hs.1))
            (le_of_lt (Real.exp_pos _))
        _ = (Real.exp (w * s) / a) * ρ ^ (n + 1) := by ring
        _ ≤ max (1 / a) (Real.exp (w * x) / a) * ρ ^ (n + 1) :=
          mul_le_mul_of_nonneg_right hE (pow_nonneg hρ0 _)
