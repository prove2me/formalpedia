-- Prove2me | solution 1 for Comp.LeakyGate.gate_AF_le_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:37:32.310807+00:00
-- url     : https://prove2.me/submissions/4161019e-5cf7-4075-80a4-06c6622a1038

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_LeakyGateQ
import Theorems.Thm_Comp_LeakyGate_gate_nonzero
import Theorems.Thm_Comp_CsgQ_AF_le_univ
import Theorems.Thm_Comp_ModelData_AF_le_of_data_step


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.LeakyGate
namespace Comp.LeakyGate
theorem _root_.solution :
    (gate.toCsgQ.toCSG gate_wf).AF ↑gateTarget ≤ (↑gateGood : Set (Fin gate.nStates)) :=
  gate.AF_le_of_data_step gate_shape gate_stochastic gate_nonzero gateTarget Finset.univ
    gateGood 2 (by decide) (by decide) (CsgQ.AF_le_univ gate.toCsgQ gate_wf gateTarget)
end Comp.LeakyGate
