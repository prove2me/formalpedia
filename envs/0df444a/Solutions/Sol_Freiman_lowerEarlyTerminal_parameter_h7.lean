-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_parameter_h7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T20:54:03.23399+00:00
-- url     : https://prove2.me/submissions/b2d1f8c9-bdca-4d86-8ae6-456eb61ac568

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic

open Freiman

set_option maxHeartbeats 1000000 in
theorem solution (p : LowerPair) : lowerEarlyTerminalAt p [lowerEarlyTerminalH7] ↔ ¬ lowerA p 3 := by
  -- Arithmetic of `√3`, the only irrationality occurring in either threshold.
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 3 < 2 := by nlinarith [hs, hs0]
  -- The two continued-fraction steps that occur inside the four `lowerTheta` values.
  have v1 : (1:ℝ) / (3 + (Real.sqrt 3 - 1)) = 2 - Real.sqrt 3 := by
    rw [div_eq_iff (by nlinarith)]; nlinarith [hs]
  have v2 : (1:ℝ) / (1 + (2 - Real.sqrt 3)) = (3 + Real.sqrt 3) / 6 := by
    rw [div_eq_iff (by nlinarith)]; nlinarith [hs]
  -- Closed forms for the four parameters of the `lowerA p 3` threshold.
  have e3 : lowerTheta 3 = 2 - Real.sqrt 3 := by
    simp only [lowerTheta, prefixEval, lowerTau]; push_cast; rw [v1]
  have e25 : lowerTheta 25 = 5/22 + (1/22) * Real.sqrt 3 := by
    simp only [lowerTheta, prefixEval, lowerTau]; push_cast; rw [v1]
    rw [div_eq_iff (by nlinarith)]; nlinarith [hs]
  have e63 : lowerTheta 63 = 4/13 + (1/13) * Real.sqrt 3 := by
    simp only [lowerTheta, prefixEval, lowerTau]; push_cast; rw [v1]
    rw [div_eq_iff (by nlinarith)]; nlinarith [hs]
  have e66 : lowerTheta 66 = 9/13 - (1/13) * Real.sqrt 3 := by
    simp only [lowerTheta, prefixEval, lowerTau]; push_cast; rw [v1, v2]
    rw [div_eq_iff (by nlinarith)]; nlinarith [hs]
  -- `lowerEarlyTerminalH7` is a weak lower bound, so it is the negation of the
  -- strict upper bound `lowerA p 3`; the two thresholds agree coefficientwise.
  unfold lowerEarlyTerminalAt lowerA section14Holds
  simp only [List.mem_singleton, forall_eq, certBoundHolds, lowerEarlyTerminalH7,
    lowerEarlyTerminalR, lowerEarlyTerminalS, lowerEarlyTerminalQ, certThresholdVal,
    certThresholdNum, certThresholdDen, certFieldVal, lowerThreshold, Bool.false_eq_true,
    if_false, not_lt, e3, e25, e63, e66]
  push_cast
  ring_nf
