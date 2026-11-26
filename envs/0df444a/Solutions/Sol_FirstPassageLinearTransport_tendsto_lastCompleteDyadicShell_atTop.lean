-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_lastCompleteDyadicShell_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:36.231993+00:00
-- url     : https://prove2.me/submissions/73f9fd39-e276-4ffc-bf19-73efeef2ac21

import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
import Theorems.Thm_FirstPassageLinearTransport_tendsto_natLogTwo_atTop


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    Tendsto lastCompleteDyadicShell atTop atTop := by
  exact (tendsto_sub_atTop_nat 1).comp tendsto_natLogTwo_atTop
end FirstPassageLinearTransport
