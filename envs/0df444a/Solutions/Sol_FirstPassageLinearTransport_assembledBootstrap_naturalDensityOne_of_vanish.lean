-- Prove2me | solution 1 for FirstPassageLinearTransport.assembledBootstrap_naturalDensityOne_of_vanish
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:27:47.517787+00:00
-- url     : https://prove2.me/submissions/217da892-40d4-4f29-8b45-11c781c41455

import Definitions.Def_FirstPassageLinearTransport_HeadlineParameters
import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
import Theorems.Thm_FirstPassageLinearTransport_naturalDensityOne_assembleDyadic


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta : ℝ} (p : StageSetup r eta) (omega : ℝ)
    (hvanish : Filter.Tendsto
      (fun M => shellExceptionalRatio (shellBootstrap p omega M) M)
      Filter.atTop (nhds 0)) :
    NaturalDensityOne (assembledBootstrap p omega) := by
  exact naturalDensityOne_assembleDyadic (shellBootstrap p omega) hvanish
end FirstPassageLinearTransport
