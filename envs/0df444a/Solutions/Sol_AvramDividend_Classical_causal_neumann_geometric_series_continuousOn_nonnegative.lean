-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_geometric_series_continuousOn_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:52:21.331567+00:00
-- url     : https://prove2.me/submissions/ec4c4f1a-4bb3-4409-a8dd-491fcc30de6f

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_neumann_series_C1_of_signed_power_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set

/-- A uniform geometric majorant makes the damped Neumann-primitive series
continuous on the closed positive half-line and absolutely summable there. -/
theorem solution
    (H : ℕ → ℝ → ℝ) (a ρ : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcont : ∀ n : ℕ, ContinuousOn (H n) (Ici (0 : ℝ)))
    (hbound : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ, H n x) (Ici (0 : ℝ)) ∧
      (∀ x : ℝ, 0 ≤ x → Summable (fun n : ℕ => H n x)) := by
  have hρnorm : ‖ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hρ0]
    exact hρ1
  have hgeom : Summable (fun n : ℕ => ρ ^ n) :=
    summable_geometric_of_norm_lt_one hρnorm
  have hmajor : Summable (fun n : ℕ => (ρ / a) * ρ ^ n) :=
    hgeom.mul_left (ρ / a)
  have hnorm (n : ℕ) (x : ℝ) (hx : x ∈ Ici (0 : ℝ)) :
      ‖H n x‖ ≤ (ρ / a) * ρ ^ n := by
    rw [Real.norm_eq_abs]
    calc
      |H n x| ≤ ρ ^ (n + 1) / a := hbound n x hx
      _ = (ρ / a) * ρ ^ n := by rw [pow_succ]; ring
  constructor
  · exact continuousOn_tsum hcont hmajor (fun n x hx => hnorm n x hx)
  · intro x hx
    exact Summable.of_norm_bounded hmajor (fun n => hnorm n x hx)
