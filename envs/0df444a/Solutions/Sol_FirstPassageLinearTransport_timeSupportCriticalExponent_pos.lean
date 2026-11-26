-- Prove2me | solution 1 for FirstPassageLinearTransport.timeSupportCriticalExponent_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:40:10.950838+00:00
-- url     : https://prove2.me/submissions/42e9fea2-ecff-40a3-9821-80816db1131e

import Definitions.Def_FirstPassageLinearTransport_ShrinkingHighDensity
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Theorems.Thm_FirstPassageLinearTransport_timeSupportCriticalExponent_gt_half

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    0 < timeSupportCriticalExponent :=
  lt_trans (by norm_num : (0 : ℝ) < 1 / 2)
    timeSupportCriticalExponent_gt_half
end FirstPassageLinearTransport
