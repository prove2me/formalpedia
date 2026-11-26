-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzLowerSurvivalMass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:57.527811+00:00
-- url     : https://prove2.me/submissions/3c26a943-f2b2-4f81-b50e-dab1ff6efb1f

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_lowerSurvivalMass_le_centered
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_pos
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_lt_one
import Theorems.Thm_FirstPassageLinearTransport_collatzLogIncrement_abs_le_one
import Theorems.Thm_FirstPassageLinearTransport_collatzLogIncrement_centered
import Theorems.Thm_FirstPassageLinearTransport_collatzTiltVariance_pos

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {B : ℝ} (hB : 0 ≤ B) {n : ℕ} (hn : 0 < n) :
    lowerSurvivalMass collatzTilt collatzLogIncrement (-B) n 0 ≤
      (1 + 2 / collatzTiltVariance) * (B + 1) / Real.sqrt n := by
  exact lowerSurvivalMass_le_centered
    collatzTilt_pos.le collatzTilt_lt_one.le collatzTiltVariance_pos hB
    collatzLogIncrement_abs_le_one collatzLogIncrement_centered rfl hn
end FirstPassageLinearTransport
