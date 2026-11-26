-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzFairTiltRate_eq_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:55.35329+00:00
-- url     : https://prove2.me/submissions/59e34a9d-49cb-4261-a51a-53de94add779

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    collatzFairTiltRate = Real.log 2 - Real.binEntropy collatzTilt := by
  have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold collatzFairTiltRate collatzTiltLambda Real.binEntropy collatzTilt
  rw [Real.log_inv, Real.log_inv]
  field_simp [hlog3]
  ring
end FirstPassageLinearTransport
