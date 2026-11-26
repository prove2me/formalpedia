-- Prove2me | solution 1 for FirstPassageLinearTransport.one_lt_log_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:25.681793+00:00
-- url     : https://prove2.me/submissions/4dc2d3af-d8f0-4e6e-86be-1579f209bb63

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
  exact Real.exp_one_lt_three
end FirstPassageLinearTransport
