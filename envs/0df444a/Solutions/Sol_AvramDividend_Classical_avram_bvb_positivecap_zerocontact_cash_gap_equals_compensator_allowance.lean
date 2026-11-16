-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_positivecap_zerocontact_cash_gap_equals_compensator_allowance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:05:01.262317+00:00
-- url     : https://prove2.me/submissions/8aaba736-0f39-42de-abd4-25c9f3d2d34d

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
theorem solution (T : ℝ) (hT : 0 < T) :
    (1 - Real.exp (-T)) + (1 / 2 : ℝ) * Real.exp (-T) =
      (1 / 2 : ℝ) + (1 / 2) * (1 - Real.exp (-T)) ∧
    0 < (1 / 2 : ℝ) * (1 - Real.exp (-T)) := by
  constructor
  · ring
  · have hE : Real.exp (-T) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    nlinarith
