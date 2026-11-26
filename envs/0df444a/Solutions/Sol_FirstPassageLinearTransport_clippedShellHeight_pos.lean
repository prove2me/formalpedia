-- Prove2me | solution 1 for FirstPassageLinearTransport.clippedShellHeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:27.290937+00:00
-- url     : https://prove2.me/submissions/44b269a4-9a43-4fa0-9a98-f4b85bf934a6

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Theorems.Thm_FirstPassageLinearTransport_dyadicShellMinimum_pos

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {R : ℕ → ℝ} (hR : ∀ n, 0 < R n) (M : ℕ) :
    0 < clippedShellHeight R M := by
  unfold clippedShellHeight
  exact lt_min (dyadicShellMinimum_pos hR M) (by positivity)
end FirstPassageLinearTransport
