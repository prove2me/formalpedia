-- Prove2me | solution 1 for Comp.LeakyGate.gate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:35:52.692478+00:00
-- url     : https://prove2.me/submissions/824c6a7c-66a2-460a-b964-4e8a7c33abb0

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_LeakyGateQ

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.LeakyGate
namespace Comp.LeakyGate
theorem _root_.solution : gate.Nonneg := by
  intro s
  fin_cases s <;>
    norm_num [ModelData.transOf, ModelData.stateAt, or_imp, and_imp, forall_and,
      forall_eq']
end Comp.LeakyGate
