-- Prove2me | solution 1 for Comp.LeakyGate.gate_answers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:36:38.823797+00:00
-- url     : https://prove2.me/submissions/775062d3-8489-40d6-afdf-22d802f35828

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_LeakyGateQ
import Theorems.Thm_Comp_LeakyGate_gate_nonzero
import Theorems.Thm_Comp_ModelData_answers_sureSafe_of_fix


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.LeakyGate
namespace Comp.LeakyGate
theorem _root_.solution :
    gate.toCsgQ.Answers gate_wf (Objective.sureSafe gateSafe) (Answer.region gateGood) :=
  gate.answers_sureSafe_of_fix gate_shape gate_stochastic gate_nonzero gateSafe gateGood
    (by decide)
end Comp.LeakyGate
