-- Prove2me | solution 1 for FirstPassageLinearTransport.assembledBootstrap_actual_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:44.095309+00:00
-- url     : https://prove2.me/submissions/e4b9a870-f83d-4df7-a01c-5e3e6f1164d1

import Definitions.Def_FirstPassageLinearTransport_HeadlineParameters
import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_eq_orbit_stageClock


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta : ℝ} (p : StageSetup r eta) {omega : ℝ} {n : ℕ}
    : stageOrbit p (stageCount omega (Nat.log 2 n)) n =
      orbit (stageClock p (stageCount omega (Nat.log 2 n)) n) n :=
  stageOrbit_eq_orbit_stageClock _ _ _
end FirstPassageLinearTransport
