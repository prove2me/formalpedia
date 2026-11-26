-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.central_window_le_log_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:39:27.469609+00:00
-- url     : https://prove2.me/submissions/fe69f26b-a5aa-471e-be4e-b8a4b4c6f42d

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_central_window_upper

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ} {eta : ℝ}
    (hcen : InCentralRenyiWindow N s eta)
    (hsize :
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N) :
    (s : ℝ) ≤ (Real.log 2 / Real.log 3) * N := by
  have hupper := central_window_upper hcen
  linarith
end CollatzEndpointTransport.FixedTotal
