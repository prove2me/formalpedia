-- Prove2me | solution 1 for FirstPassageLinearTransport.extendedWindow_powerDense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:03.165374+00:00
-- url     : https://prove2.me/submissions/6130cc51-a7f5-43bf-bd39-e4b49fd54d20

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Theorems.Thm_FirstPassageLinearTransport_initialWindowGood_subset_extendedWindow
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_mono_set
import Theorems.Thm_FirstPassageLinearTransport_initialWindowGood_powerDense


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r eta : ℝ}
    (p : StageSetup r eta) :
    PowerDense (extendedWindow p)
      (quadraticWindowGlobalConstant eta)
      (quadraticWindowDensityRate eta) :=
  (initialWindowGood_powerDense p.eta_pos p.eta_le_one).mono_set
    (initialWindowGood_subset_extendedWindow p)
end FirstPassageLinearTransport
