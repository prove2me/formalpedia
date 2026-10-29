-- Prove2me | solution 1 for AvramDividend.Classical.esscher_shift_domain_of_convex_chord
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:46:15.579505+00:00
-- url     : https://prove2.me/submissions/818219af-3a0c-46cd-aaf3-1c4c31ff20e7

import Mathlib

theorem solution
    (ψ : ℝ → ℝ) (q φ θ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hθ : 0 < θ)
    (hroot : ψ φ = q) (hzero : ψ 0 = 0)
    (hchord : ψ φ ≤ (φ / (φ + θ)) * ψ (φ + θ) + (θ / (φ + θ)) * ψ 0) :
    q < ψ (φ + θ) := by
  rw [hzero, mul_zero, add_zero, hroot, div_mul_eq_mul_div, le_div_iff₀ (by linarith)] at hchord
  nlinarith
