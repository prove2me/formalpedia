-- Prove2me | solution 1 for DarkEnergyLCDM.no_acceleration_without_lambda
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:14:44.093033+00:00
-- url     : https://prove2.me/submissions/9b31c01a-ec45-4ebe-b12a-3e532cec8584

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

open DarkEnergyLCDM

theorem solution (G : ℝ) (hG : 0 < G) (a ρ p : ℝ → ℝ) (t : ℝ)
    (ha : 0 < a t) (hρ : 0 ≤ ρ t) (hp : 0 ≤ p t)
    (hacc : AccelerationEq G 0 a ρ p t) :
    deriv (deriv a) t ≤ 0 := by
  unfold AccelerationEq at hacc
  have h1 : deriv (deriv a) t / a t ≤ 0 := by
    rw [hacc]
    have : 0 ≤ 4 * Real.pi * G / 3 * (ρ t + 3 * p t) := by positivity
    linarith
  by_contra hc
  rw [not_le] at hc
  have := div_pos hc ha
  linarith
