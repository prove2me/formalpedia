-- Prove2me | solution 1 for AvramDividend.Classical.causal_exp_damped_signed_kernel_untwist
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:44:41.671058+00:00
-- url     : https://prove2.me/submissions/4b73ed38-2036-4f6c-b3a0-a3d91a58c703

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real

/-- Exponential untilting recovers the Gaussian signed kernel. -/
theorem solution
    (a w β : ℝ) (K : ℝ → ℝ) (t : ℝ) (ht : 0 < t) :
    Real.exp (w * t) *
      (if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0) =
        -a⁻¹ * (β + K t) := by
  simp only [if_pos ht]
  have he : Real.exp (w * t) * Real.exp (-w * t) = 1 := by
    rw [← Real.exp_add]
    have hz : w * t + -w * t = 0 := by ring
    rw [hz, Real.exp_zero]
  calc
    Real.exp (w * t) * -(a⁻¹ * Real.exp (-w * t) * (β + K t)) =
      -(a⁻¹ * (Real.exp (w * t) * Real.exp (-w * t)) * (β + K t)) := by ring
    _ = -a⁻¹ * (β + K t) := by rw [he]; ring
