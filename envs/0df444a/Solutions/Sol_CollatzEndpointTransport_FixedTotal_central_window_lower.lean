-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.central_window_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:50:05.264384+00:00
-- url     : https://prove2.me/submissions/8f398a33-564b-4d11-9c80-f4e536eeaca0

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
    (1 / 2 - eta) * N + 1 / 2 ≤ (s : ℝ) := by
  unfold InCentralRenyiWindow at hcen
  have hlower := (abs_le.mp hcen).1
  push_cast at hlower
  linarith
end CollatzEndpointTransport.FixedTotal
