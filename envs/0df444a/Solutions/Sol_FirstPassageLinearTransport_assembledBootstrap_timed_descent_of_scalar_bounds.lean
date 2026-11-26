-- Prove2me | solution 1 for FirstPassageLinearTransport.assembledBootstrap_timed_descent_of_scalar_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:14:13.994979+00:00
-- url     : https://prove2.me/submissions/83ee8347-efc0-4832-b65d-b27fa981ac36

import Definitions.Def_FirstPassageLinearTransport_HeadlineParameters
import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
import Theorems.Thm_FirstPassageLinearTransport_assembledBootstrap_actual_endpoint

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta delta omega clock : ℝ} (p : StageSetup r eta) {n : ℕ}
    (hlanding :
      (stageOrbit p (stageCount omega (Nat.log 2 n)) n : ℝ) ≤
        Real.exp ((Real.log n) ^ (1 - delta)))
    (htime :
      (stageClock p (stageCount omega (Nat.log 2 n)) n : ℝ) <
        clock * Real.log n) :
    HasTimedStretchedLogDescent delta clock n := by
  refine ⟨stageClock p (stageCount omega (Nat.log 2 n)) n, htime, ?_⟩
  rw [← assembledBootstrap_actual_endpoint p]
  exact hlanding
end FirstPassageLinearTransport
