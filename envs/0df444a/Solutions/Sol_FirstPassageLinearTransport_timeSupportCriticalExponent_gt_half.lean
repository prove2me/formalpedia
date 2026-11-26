-- Prove2me | solution 1 for FirstPassageLinearTransport.timeSupportCriticalExponent_gt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:38:52.817997+00:00
-- url     : https://prove2.me/submissions/e009b0dc-b121-4fb9-a9a1-eb4d067d8f63

import Definitions.Def_FirstPassageLinearTransport_ShrinkingHighDensity
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Theorems.Thm_FirstPassageLinearTransport_fixedPolylogCriticalExponent_gt_one


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    1 / 2 < timeSupportCriticalExponent := by
  unfold timeSupportCriticalExponent
  linarith [fixedPolylogCriticalExponent_gt_one]
end FirstPassageLinearTransport
