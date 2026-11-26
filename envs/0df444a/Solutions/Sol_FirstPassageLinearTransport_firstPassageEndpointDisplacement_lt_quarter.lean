-- Prove2me | solution 1 for FirstPassageLinearTransport.firstPassageEndpointDisplacement_lt_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:03:26.580195+00:00
-- url     : https://prove2.me/submissions/77a9511e-661a-4666-bfa3-06571455ba7c

import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Theorems.Thm_FirstPassageLinearTransport_three_halves_lt_logTwoThree
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_logTwoThree_one_lt


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    firstPassageEndpointDisplacement < 1 / 4 := by
  have ha0 : (3 / 4 : ℝ) < a0 := by
    unfold a0
    linarith [three_halves_lt_logTwoThree]
  have hgap : driftGap < 1 / 4 := by
    unfold driftGap
    linarith
  unfold firstPassageEndpointDisplacement
  have hlogOne : 1 < logTwoThree := logTwoThree_one_lt
  calc
    driftGap / logTwoThree < driftGap :=
      (div_lt_self driftGap_pos hlogOne)
    _ < 1 / 4 := hgap
end FirstPassageLinearTransport
