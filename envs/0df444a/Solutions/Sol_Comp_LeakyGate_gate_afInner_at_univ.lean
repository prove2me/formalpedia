-- Prove2me | solution 1 for Comp.LeakyGate.gate_afInner_at_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:36:50.996595+00:00
-- url     : https://prove2.me/submissions/e4dc3513-296b-48a9-bf27-f77dd5692174

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_LeakyGateQ
import Theorems.Thm_Comp_LeakyGate_gate_nonzero
import Theorems.Thm_Comp_ModelData_afInner_eq_of_data


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.LeakyGate
namespace Comp.LeakyGate
theorem _root_.solution :
    ((gate.toCsgQ.toCSG gate_wf).AFInner ↑gateTarget
        ↑(Finset.univ : Finset (Fin gate.nStates))).lfp = (↑gateGood : Set (Fin gate.nStates)) :=
  gate.afInner_eq_of_data gate_shape gate_stochastic gate_nonzero gateTarget Finset.univ
    gateGood 2 (by decide) (by decide)
end Comp.LeakyGate
