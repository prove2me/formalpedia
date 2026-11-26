-- Prove2me | solution 1 for FirstPassageLinearTransport.rpowLogScheduleIdentity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:44:10.027801+00:00
-- url     : https://prove2.me/submissions/c6afbdcf-16ee-49ca-96bc-2bd07ffaa62a

import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {chi omega x : ℝ} (hchi : 0 < chi) (hx : 0 < x) :
    chi ^ (omega * Real.log x) =
      x ^ (-densityGamma omega chi) := by
  rw [Real.rpow_def_of_pos hchi, Real.rpow_def_of_pos hx]
  unfold densityGamma
  rw [one_div, Real.log_inv]
  congr 1
  ring
end FirstPassageLinearTransport
