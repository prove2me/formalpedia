-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_reciprocal_log_sandwich_algebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:45:40.593889+00:00
-- url     : https://prove2.me/submissions/f8c5f943-0300-406a-aa71-d472997b92fd

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real

/-- Ordered positive reciprocal record factors constrain the logarithmic
scale increment between their unit-height power logarithms. -/
theorem solution
    (n : ℕ) (u v w z : ℝ)
    (hu : 0 < u) (hv : 0 < v)
    (hw : 0 < w) (hz : 0 < z)
    (hlo : u ≤ w / z) (hhi : w / z ≤ v) :
    -Real.log (v ^ (n + 1)) ≤
        ((n : ℝ) + 1) * (Real.log z - Real.log w) ∧
      ((n : ℝ) + 1) * (Real.log z - Real.log w) ≤
        -Real.log (u ^ (n + 1)) := by
  have hdiv : 0 < w / z := div_pos hw hz
  have hloglo : Real.log u ≤ Real.log (w / z) :=
    Real.log_le_log hu hlo
  have hloghi : Real.log (w / z) ≤ Real.log v :=
    Real.log_le_log hdiv hhi
  have hlogdiv : Real.log (w / z) =
      Real.log w - Real.log z :=
    Real.log_div (ne_of_gt hw) (ne_of_gt hz)
  rw [hlogdiv] at hloglo hloghi
  have hmult : 0 ≤ (n : ℝ) + 1 := by positivity
  have hpowl : Real.log (u ^ (n + 1)) =
      ((n : ℝ) + 1) * Real.log u := by
    rw [Real.log_pow]
    push_cast
    ring
  have hpowr : Real.log (v ^ (n + 1)) =
      ((n : ℝ) + 1) * Real.log v := by
    rw [Real.log_pow]
    push_cast
    ring
  have hL : 0 ≤ ((n : ℝ) + 1) *
      (Real.log w - Real.log z - Real.log u) :=
    mul_nonneg hmult (by linarith)
  have hR : 0 ≤ ((n : ℝ) + 1) *
      (Real.log v - (Real.log w - Real.log z)) :=
    mul_nonneg hmult (by linarith)
  rw [hpowl, hpowr]
  constructor <;> nlinarith [hL, hR]
