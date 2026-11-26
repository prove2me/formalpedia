-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzTilt_lt_two_thirds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:33:11.100807+00:00
-- url     : https://prove2.me/submissions/9c55dbb8-8247-48b9-91b3-67ae569d81e7

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution : collatzTilt < 2 / 3 := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [collatzTilt, div_lt_iff₀ hlog3]
  have hlog : Real.log 8 < Real.log 9 :=
    Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 8))
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 9))
      (by norm_num)
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 * (2 * 2) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [h8, h9] at hlog
  nlinarith
end FirstPassageLinearTransport
