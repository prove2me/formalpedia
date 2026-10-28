-- Prove2me | solution 1 for AvramDividend.Classical.exponential_right_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:31:05.600519+00:00
-- url     : https://prove2.me/submissions/47130460-3b78-4e8e-b872-60241b2478be

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Positivity
open Filter Topology
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A continuous exponential lower squeeze as a positive time shift vanishes. -/
theorem solution
    (t lambda c : ℝ)
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      Real.exp (-((t + epsilon) * lambda)) ≤ c)
    (hUpper : c ≤ Real.exp (-(t * lambda))) :
    c = Real.exp (-(t * lambda)) := by
  have hEps :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hSum :
      Tendsto (fun n : ℕ => t + (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 (t + 0)) :=
    tendsto_const_nhds.add hEps
  have hArg :
      Tendsto (fun n : ℕ =>
        -((t + (1 : ℝ) / ((n : ℝ) + 1)) * lambda))
        atTop (𝓝 (-(t * lambda))) := by
    simpa only [add_zero] using
      ((hSum.mul (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => lambda) atTop (𝓝 lambda))).neg)
  have hLimit :
      Tendsto (fun n : ℕ =>
        Real.exp (-((t + (1 : ℝ) / ((n : ℝ) + 1)) * lambda)))
        atTop (𝓝 (Real.exp (-(t * lambda)))) :=
    (Real.continuous_exp.tendsto _).comp hArg
  have hBound :
      ∀ᶠ n : ℕ in atTop,
        Real.exp (-((t + (1 : ℝ) / ((n : ℝ) + 1)) * lambda)) ≤ c := by
    exact Filter.Eventually.of_forall (fun n =>
      hLower ((1 : ℝ) / ((n : ℝ) + 1)) (by positivity))
  exact le_antisymm hUpper (le_of_tendsto hLimit hBound)
