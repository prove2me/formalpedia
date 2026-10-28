-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_resolvent_kernel_nonneg_of_tilted_monotone_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:31:41.997104+00:00
-- url     : https://prove2.me/submissions/a370b0cd-ddae-4a01-907a-0cbc5026622e

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Interval.Set.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real Set

/-- Tilted-scale monotonicity implies nonnegativity of the spatial resolvent kernel
on the triangle of nonnegative initial reserve and spatial argument. -/
theorem solution
    (θ : ℝ) (W : ℝ → ℝ)
    (hmono : MonotoneOn (fun z : ℝ => Real.exp (-(θ * z)) * W z) (Ici (0 : ℝ)))
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ x) :
    0 ≤ Real.exp (-(θ * y)) * W x - W (x - y) := by
  have hsub : 0 ≤ x - y := by linarith
  have hle :
      Real.exp (-(θ * (x - y))) * W (x - y) ≤
      Real.exp (-(θ * x)) * W x := by
    exact hmono (by simpa using hsub) (by simpa using hx) (by linarith)
  have hscaled := mul_le_mul_of_nonneg_right hle
    (le_of_lt (Real.exp_pos (θ * (x - y))))
  have hleft :
      (Real.exp (-(θ * (x - y))) * W (x - y)) *
        Real.exp (θ * (x - y)) = W (x - y) := by
    calc
      _ = (Real.exp (-(θ * (x - y))) *
            Real.exp (θ * (x - y))) * W (x - y) := by ring
      _ = W (x - y) := by
        rw [← Real.exp_add]
        have hz : -(θ * (x - y)) + θ * (x - y) = 0 := by ring
        rw [hz, Real.exp_zero, one_mul]
  have hright :
      (Real.exp (-(θ * x)) * W x) *
        Real.exp (θ * (x - y)) =
      Real.exp (-(θ * y)) * W x := by
    calc
      _ = (Real.exp (-(θ * x)) *
            Real.exp (θ * (x - y))) * W x := by ring
      _ = Real.exp (-(θ * y)) * W x := by
        rw [← Real.exp_add]
        have hz : -(θ * x) + θ * (x - y) = -(θ * y) := by ring
        rw [hz]
  rw [hleft, hright] at hscaled
  linarith
