-- Prove2me | solution 1 for Comp.LeakyGate.gate_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:17:41.935916+00:00
-- url     : https://prove2.me/submissions/bfe942ad-df60-40d7-954c-6e24364ed275

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_LeakyGateQ

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.LeakyGate
namespace Comp.LeakyGate
theorem _root_.solution : gate.Nonzero := by
  intro s
  fin_cases s <;>
    norm_num [ModelData.transOf, ModelData.stateAt, or_imp, and_imp, forall_and,
      forall_eq']
end Comp.LeakyGate
