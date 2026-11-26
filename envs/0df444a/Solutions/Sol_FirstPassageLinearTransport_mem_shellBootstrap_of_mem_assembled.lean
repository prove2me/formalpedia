-- Prove2me | solution 1 for FirstPassageLinearTransport.mem_shellBootstrap_of_mem_assembled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:20.548011+00:00
-- url     : https://prove2.me/submissions/b8faccdc-ded3-438a-a6d7-994cf313a9db

import Definitions.Def_FirstPassageLinearTransport_HeadlineParameters
import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta : ℝ} (p : StageSetup r eta) {omega : ℝ} {n : ℕ}
    (hn : n ∈ assembledBootstrap p omega) :
    n ∈ bootstrapSet p (stageCount omega (Nat.log 2 n)) := by
  exact hn
end FirstPassageLinearTransport
