-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzTilt_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:27:48.947515+00:00
-- url     : https://prove2.me/submissions/7adc5698-996e-4687-bf88-ee963fc29668

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution : collatzTilt < 1 := by
  unfold collatzTilt
  rw [div_lt_one (Real.log_pos (by norm_num : (1 : ℝ) < 3))]
  exact Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2))
    (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 3))
    (by norm_num)
end FirstPassageLinearTransport
