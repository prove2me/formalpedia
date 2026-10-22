-- Prove2me | solution 1 for AvramDividend.Classical.exp_dividend_secant_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:22:55.473393+00:00
-- url     : https://prove2.me/submissions/7d8d87d1-82c0-41de-9090-9e92e1240277

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (θ u a : ℝ) (hθ : 1 ≤ θ) (ha : 0 ≤ a) (hua : a ≤ u) :
    a ≤ Real.exp (θ * u) - Real.exp (θ * (u - a)) := by
  have hθ0 : 0 ≤ θ := by linarith
  have hua0 : 0 ≤ u - a := by linarith
  have hθua : 0 ≤ θ * (u - a) := mul_nonneg hθ0 hua0
  have he : 1 ≤ Real.exp (θ * (u - a)) := by
    have h := Real.add_one_le_exp (θ * (u - a))
    linarith
  have hd : a ≤ Real.exp (θ * a) - 1 := by
    have h := Real.add_one_le_exp (θ * a)
    have hmul := mul_nonneg (sub_nonneg.mpr hθ) ha
    nlinarith
  have hd0 : 0 ≤ Real.exp (θ * a) - 1 := by linarith
  have hprod :
      Real.exp (θ * (u - a)) * Real.exp (θ * a) =
        Real.exp (θ * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    a ≤ Real.exp (θ * a) - 1 := hd
    _ ≤ Real.exp (θ * (u - a)) * (Real.exp (θ * a) - 1) := by
      have hm := mul_nonneg (sub_nonneg.mpr he) hd0
      nlinarith
    _ = Real.exp (θ * u) - Real.exp (θ * (u - a)) := by
      rw [mul_sub, mul_one, hprod]
