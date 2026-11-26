-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.central_window_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:37:16.01769+00:00
-- url     : https://prove2.me/submissions/2176a52f-73a7-4721-b6f9-695e941bc274

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ} {eta : ℝ}
    (hcen : InCentralRenyiWindow N s eta) :
    (s : ℝ) ≤ (1 / 2 + eta) * N + 1 / 2 := by
  unfold InCentralRenyiWindow at hcen
  have hupper := (abs_le.mp hcen).2
  push_cast at hupper
  linarith
end CollatzEndpointTransport.FixedTotal
