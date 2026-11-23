-- Prove2me | solution 1 for Comp.chain_step3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:49:54.400238+00:00
-- url     : https://prove2.me/submissions/7d57e844-c615-4f8f-837d-480ef34c7949

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
import Theorems.Thm_Comp_gStepF_eq

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution : chainGame.gStepF chainSafe chainR2 = chainR3 := by
  rw [gStepF_eq]; decide
end Comp
