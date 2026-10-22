-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_time_weight_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:52:37.75682+00:00
-- url     : https://prove2.me/submissions/16e1ddfc-5671-46a8-ad93-cdff8e7e8d96

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal

/-- Factor the strictly positive time-dependent Laplace weight out of each double-tail jump atom. -/
theorem solution (φ θ t z : ℝ) :
    (if 0 < t ∧ t < z then
      ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
        ENNReal.ofReal (Real.exp (-φ * z))
     else 0) =
    ENNReal.ofReal (Real.exp (-θ * t)) *
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) := by
  by_cases h : 0 < t ∧ t < z
  · simp only [if_pos h]
    rw [ENNReal.ofReal_mul (by linarith : 0 ≤ z - t)]
    ac_rfl
  · simp [h]
