-- Prove2me | solution 1 for FirstPassageLinearTransport.pullbackShellConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:53.741798+00:00
-- url     : https://prove2.me/submissions/87fbe8b7-088c-49e2-9289-44198e4836f5

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Theorems.Thm_FirstPassageLinearTransport_extendedWindow_powerDense
import Theorems.Thm_FirstPassageLinearTransport_transportGap_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_C_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r eta chi Dc : ℝ}
    (p : StageSetup r eta) (hchi : chi < r) :
    0 < pullbackShellConstant p chi Dc := by
  unfold pullbackShellConstant
  have hq := transportGap_pos hchi
  have hW := extendedWindow_powerDense p
  have hC := hW.C_pos
  positivity
end FirstPassageLinearTransport
