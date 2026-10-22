-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_compensated_jump_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:30:17.731322+00:00
-- url     : https://prove2.me/submissions/866190b0-0d81-4ba0-a174-a419adfc5ae2

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Quadratic small-jump envelope for the negative exponential compensator. -/
theorem solution
    (θ z : ℝ) (hθ : 0 ≤ θ) (hz : 0 ≤ z) :
    Real.exp (-θ * z) - 1 + θ * z ≤ (θ * z) ^ 2 := by
  let u : ℝ := θ * z
  have hu : 0 ≤ u := mul_nonneg hθ hz
  have hpos : 0 < 1 + u := by linarith
  have hExp : (1 + u) * Real.exp (-u) ≤ 1 := by
    have hh := Real.add_one_le_exp u
    have hh' := mul_le_mul_of_nonneg_right hh
      (le_of_lt (Real.exp_pos (-u)))
    have heq : Real.exp u * Real.exp (-u) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      (1 + u) * Real.exp (-u) = (u + 1) * Real.exp (-u) := by ring
      _ ≤ Real.exp u * Real.exp (-u) := hh'
      _ = 1 := heq
  have hPoly : 1 ≤ (1 + u) * (1 - u + u ^ 2) := by
    nlinarith [pow_nonneg hu 3]
  have hcalc : (1 + u) * Real.exp (-u) ≤
      (1 + u) * (1 - u + u ^ 2) :=
    le_trans hExp hPoly
  have hle : Real.exp (-u) ≤ 1 - u + u ^ 2 :=
    (mul_le_mul_iff_of_pos_left hpos).mp hcalc
  have hfinish : Real.exp (-u) - 1 + u ≤ u ^ 2 := by
    linarith [hle]
  simpa only [u, neg_mul] using hfinish
