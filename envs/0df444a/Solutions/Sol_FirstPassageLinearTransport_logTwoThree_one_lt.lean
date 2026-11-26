-- Prove2me | solution 1 for FirstPassageLinearTransport.logTwoThree_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:10:39.466856+00:00
-- url     : https://prove2.me/submissions/235e8b99-9777-4253-a3d5-5cb105180ae2

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution : 1 < logTwoThree := by
  unfold logTwoThree
  rw [one_lt_div (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  exact Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2))
    (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 3))
    (by norm_num)
end FirstPassageLinearTransport
