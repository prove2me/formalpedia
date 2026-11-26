-- Prove2me | solution 1 for FirstPassageLinearTransport.transportGap_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:09:17.962804+00:00
-- url     : https://prove2.me/submissions/f4e8cc15-f849-44b0-8733-d03c983b5a1f

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r chi : ℝ} (hchi : chi < r) :
    0 < transportGap r chi := by
  unfold transportGap
  exact mul_pos (sub_pos.mpr hchi) (Real.log_pos (by norm_num))
end FirstPassageLinearTransport
