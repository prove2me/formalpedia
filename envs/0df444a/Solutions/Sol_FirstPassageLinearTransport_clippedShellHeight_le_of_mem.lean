-- Prove2me | solution 1 for FirstPassageLinearTransport.clippedShellHeight_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:33.976545+00:00
-- url     : https://prove2.me/submissions/050ebef8-0bf2-4d31-83d6-c881cd084707

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Theorems.Thm_FirstPassageLinearTransport_dyadicShellMinimum_le_of_mem

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (R : ℕ → ℝ) {M n : ℕ} (hn : n ∈ dyadicShell M) :
    clippedShellHeight R M ≤ R n :=
  (min_le_left _ _).trans (dyadicShellMinimum_le_of_mem R hn)
end FirstPassageLinearTransport
