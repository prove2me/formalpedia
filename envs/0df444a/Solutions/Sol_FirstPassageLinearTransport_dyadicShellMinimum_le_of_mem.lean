-- Prove2me | solution 1 for FirstPassageLinearTransport.dyadicShellMinimum_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:50:56.183852+00:00
-- url     : https://prove2.me/submissions/4083ff10-d44d-4782-ad2b-e27aca71141c

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (U : ℕ → ℝ) {M n : ℕ} (hn : n ∈ dyadicShell M) :
    dyadicShellMinimum U M ≤ U n := by
  unfold dyadicShellMinimum
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
end FirstPassageLinearTransport
