-- Prove2me | solution 1 for FirstPassageLinearTransport.a0_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:08:41.511814+00:00
-- url     : https://prove2.me/submissions/dd016fba-cd4e-43f9-aedd-d405e079445d

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution : a0 < 1 := by
  unfold a0 logTwoThree
  rw [div_div, div_lt_one (by positivity)]
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  calc
    Real.log 3 < Real.log 4 := Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 3))
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 4))
      (by norm_num)
    _ = Real.log 2 * 2 := by rw [hlog4]; ring
end FirstPassageLinearTransport
