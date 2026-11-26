-- Prove2me | solution 1 for FirstPassageLinearTransport.three_halves_lt_logTwoThree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:00:23.108005+00:00
-- url     : https://prove2.me/submissions/c48f8d7b-dce6-472b-b95f-1a403bd508e4

import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution : (3 / 2 : ℝ) < logTwoThree := by
  have hlog : Real.log (8 : ℝ) < Real.log (9 : ℝ) :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 * 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hlog9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hlog8, hlog9] at hlog
  unfold logTwoThree
  exact (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 (by
    linarith)
end FirstPassageLinearTransport
