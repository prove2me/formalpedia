-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_real_exponential_weighted_poisson_coefficient_hasSum_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T19:02:16.162627+00:00
-- url     : https://prove2.me/submissions/b71c0b9f-c770-4fcc-ab5d-79cdc6bb0771

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory
open scoped BigOperators
noncomputable section

/-- The ordinary exponential has its exact real Poisson-weighted coefficient series. -/
theorem solution (r q z : ℝ) :
    HasSum (fun k : ℕ =>
        z ^ k * (Real.exp (-r) * (q ^ k / (k.factorial : ℝ))))
      (Real.exp (q * z - r)) := by
  have hExp :
      HasSum (fun k : ℕ => (q * z) ^ k / (k.factorial : ℝ))
        (Real.exp (q * z)) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (q * z))
  have hScaled := hExp.mul_left (Real.exp (-r))
  have hValue :
      Real.exp (-r) * Real.exp (q * z) =
        Real.exp (q * z - r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hTerm : (fun k : ℕ =>
      z ^ k * (Real.exp (-r) * (q ^ k / (k.factorial : ℝ)))) =
      (fun k : ℕ =>
        Real.exp (-r) * ((q * z) ^ k / (k.factorial : ℝ))) := by
    funext k
    rw [mul_pow]
    ring
  rw [hTerm, ← hValue]
  exact hScaled
