-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_real_void_semigroup_exp_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:04:16.132614+00:00
-- url     : https://prove2.me/submissions/d660ce01-a809-44bd-bf59-6d9ee3d4b4c1

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal

/-- The analytic limit in the genuine marked-count void-semigroup argument. -/
theorem solution
    (p : ℝ≥0 → ℝ) (T : ℝ≥0) (rate : ℝ)
    (hPower : ∀ n : ℕ, 0 < n → p T = (p (T / (n : ℝ≥0))) ^ n)
    (hSlope : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) * (1 - p (T / (n : ℝ≥0))))
      Filter.atTop (nhds ((T : ℝ) * rate))) :
    p T = Real.exp (-((T : ℝ) * rate)) := by
  have hNeg : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) * (p (T / (n : ℝ≥0)) - 1))
      Filter.atTop (nhds (-((T : ℝ) * rate))) := by
    have hEq :
        (fun n : ℕ => (n : ℝ) * (p (T / (n : ℝ≥0)) - 1)) =
        (fun n : ℕ => -((n : ℝ) * (1 - p (T / (n : ℝ≥0))))) := by
      funext n
      ring
    rw [hEq]
    exact hSlope.neg
  have hExp : Filter.Tendsto
      (fun n : ℕ => (1 + (p (T / (n : ℝ≥0)) - 1)) ^ n)
      Filter.atTop (nhds (Real.exp (-((T : ℝ) * rate)))) :=
    Real.tendsto_one_add_pow_exp_of_tendsto hNeg
  have hConst : Filter.Tendsto
      (fun _ : ℕ => p T) Filter.atTop
      (nhds (Real.exp (-((T : ℝ) * rate)))) := by
    apply hExp.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := by omega
    calc
      (1 + (p (T / (n : ℝ≥0)) - 1)) ^ n =
          (p (T / (n : ℝ≥0))) ^ n := by congr 1; ring
      _ = p T := (hPower n hnpos).symm
  exact tendsto_nhds_unique tendsto_const_nhds hConst
