-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzTiltLambda_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:34:29.752533+00:00
-- url     : https://prove2.me/submissions/f7907980-66a2-46dc-af70-9e2609b9bab9

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_pos
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_lt_one
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_half_lt

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution : 0 < collatzTiltLambda := by
  unfold collatzTiltLambda
  apply div_pos
  · apply sub_pos.mpr
    exact Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (sub_pos.mpr collatzTilt_lt_one))
      (Set.mem_Ioi.mpr collatzTilt_pos)
      (by linarith [collatzTilt_half_lt])
  · exact Real.log_pos (by norm_num)
end FirstPassageLinearTransport
