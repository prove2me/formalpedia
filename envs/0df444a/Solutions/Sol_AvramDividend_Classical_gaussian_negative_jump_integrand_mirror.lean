-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_negative_jump_integrand_mirror
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:27:29.284421+00:00
-- url     : https://prove2.me/submissions/5141bd82-3896-4448-905e-de077112240f

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Reversing the sign of a negative Lévy jump preserves the exact
open-interval truncation in the canonical Lévy–Khintchine integrand. -/
theorem solution (θ y : ℝ) (hy : y < 0) :
    Real.exp (θ * y) - 1 -
      θ * y * (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y =
    Real.exp (-θ * (-y)) - 1 +
      θ * (if -y < 1 then -y else 0) := by
  by_cases hsmall : -y < 1
  · have hmem : y ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by linarith, by linarith⟩
    rw [Set.indicator_of_mem hmem, if_pos hsmall]
    simp only [Pi.one_apply, mul_one]
    have harg : -θ * (-y) = θ * y := by ring
    rw [harg]
    ring
  · have hnotmem : y ∉ Ioo (-1 : ℝ) 1 := by
      intro h
      exact hsmall (by linarith [h.1])
    simp only [Set.indicator, if_neg hnotmem, if_neg hsmall]
    simp only [mul_zero, sub_zero]
    have harg : -θ * (-y) = θ * y := by ring
    rw [harg]
    ring
