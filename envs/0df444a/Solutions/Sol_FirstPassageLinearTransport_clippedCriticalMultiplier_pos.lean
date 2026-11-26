-- Prove2me | solution 1 for FirstPassageLinearTransport.clippedCriticalMultiplier_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:35:24.568193+00:00
-- url     : https://prove2.me/submissions/5664b978-a406-43c5-90eb-d0a907e9c749

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
    {U : ℕ → ℝ} (hU : ∀ n, 0 < U n) (M : ℕ) :
    0 < clippedCriticalMultiplier U M := by
  unfold clippedCriticalMultiplier
  exact lt_min
    (Real.sqrt_pos.2 (dyadicShellMinimum_pos hU M)) (by positivity)
end FirstPassageLinearTransport
