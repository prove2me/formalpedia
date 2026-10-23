-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_unweighted_atom_area
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T11:51:39.065197+00:00
-- url     : https://prove2.me/submissions/3760ac24-5e81-44b9-8d84-5f66790c9738

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory intervalIntegral

theorem solution (z : ℝ) :
    (∫ t in (0 : ℝ)..z, z - t) = z ^ 2 / 2 := by
  have hc : IntervalIntegrable (fun _ : ℝ => z) volume 0 z :=
    intervalIntegrable_const
  have hi : IntervalIntegrable (fun t : ℝ => t) volume 0 z :=
    continuous_id.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hc hi]
  rw [intervalIntegral.integral_const, integral_id]
  simp
  ring
