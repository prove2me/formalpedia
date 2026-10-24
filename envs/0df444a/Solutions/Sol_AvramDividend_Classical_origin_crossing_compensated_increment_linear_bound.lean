-- Prove2me | solution 1 for AvramDividend.Classical.origin_crossing_compensated_increment_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:09:43.686999+00:00
-- url     : https://prove2.me/submissions/5d8df5ec-88df-4b89-ba1c-31d5077388ae

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

-- The crossing increment has two first-order contributions.
theorem solution
    (W : ℝ → ℝ) (x y K : ℝ)
    (hx : 0 < x) (hy : y < 0) (hcross : x + y ≤ 0)
    (hK : 0 ≤ K)
    (hWneg : ∀ z : ℝ, z ≤ 0 → W z = 0)
    (hWval : |W x| ≤ K * x)
    (hD : |deriv W x| ≤ K) :
    |W (x + y) - W x - deriv W x * y| ≤ 2 * K * (-y) := by
  have hfirst : |W (x + y) - W x - deriv W x * y| ≤
      |W x| + |deriv W x| * (-y) := by
    calc
      _ = |(-W x) + (-(deriv W x * y))| := by
        rw [hWneg (x + y) hcross]
        ring
      _ ≤ |-W x| + |-(deriv W x * y)| := abs_add_le _ _
      _ = |W x| + |deriv W x| * (-y) := by
        rw [abs_neg, abs_neg, abs_mul, abs_of_neg hy]
  have hd : |deriv W x| * (-y) ≤ K * (-y) :=
    mul_le_mul_of_nonneg_right hD (by linarith)
  have hxle : K * x ≤ K * (-y) :=
    mul_le_mul_of_nonneg_left (by linarith [hcross]) hK
  nlinarith [hfirst, hd, hxle, hWval]
