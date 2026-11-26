-- Prove2me | solution 1 for FirstPassageLinearTransport.le_dyadicShellMinimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:09.645832+00:00
-- url     : https://prove2.me/submissions/2925a7f4-200a-472e-b361-73bfba0c160e

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
    (U : ℕ → ℝ) (M : ℕ) {b : ℝ}
    (hU : ∀ n ∈ dyadicShell M, b ≤ U n) :
    b ≤ dyadicShellMinimum U M := by
  unfold dyadicShellMinimum
  apply Finset.le_min'
  intro y hy
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
  exact hU n hn
end FirstPassageLinearTransport
