-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzTilt_half_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:32:35.667917+00:00
-- url     : https://prove2.me/submissions/dd0e0158-b4d2-43e9-9978-56d48824fdac

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution : 1 / 2 < collatzTilt := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [collatzTilt, lt_div_iff₀ hlog3]
  have hlog : Real.log 3 < Real.log 4 :=
    Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 3))
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 4))
      (by norm_num)
  rw [show (4 : ℝ) = 2 * 2 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)] at hlog
  nlinarith
end FirstPassageLinearTransport
