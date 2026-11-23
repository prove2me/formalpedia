-- Prove2me | solution 1 for Comp.LeakyGate.gate_answers_AF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:37:49.636358+00:00
-- url     : https://prove2.me/submissions/8b086762-11c7-4e7e-85d5-47437e0cbf2e

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_LeakyGateQ
import Theorems.Thm_Comp_LeakyGate_gate_nonzero
import Theorems.Thm_Comp_ModelData_answers_almostReach_of_fix


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.LeakyGate
namespace Comp.LeakyGate
theorem _root_.solution :
    gate.toCsgQ.Answers gate_wf (Objective.almostReach gateTarget) (Answer.region gateGood) :=
  gate.answers_almostReach_of_fix gate_shape gate_stochastic gate_nonzero gateTarget gateGood
    (by decide)
end Comp.LeakyGate
