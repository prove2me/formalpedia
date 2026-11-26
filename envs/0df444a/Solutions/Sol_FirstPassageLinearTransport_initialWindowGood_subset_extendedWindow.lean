-- Prove2me | solution 1 for FirstPassageLinearTransport.initialWindowGood_subset_extendedWindow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:46.47065+00:00
-- url     : https://prove2.me/submissions/d392d4af-c312-4949-ad32-f62b3879f675

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r eta : ℝ}
    (p : StageSetup r eta) :
    initialWindowGood eta ⊆ extendedWindow p :=
  Set.subset_union_left
end FirstPassageLinearTransport
