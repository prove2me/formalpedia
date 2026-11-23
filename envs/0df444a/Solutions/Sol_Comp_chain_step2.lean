-- Prove2me | solution 1 for Comp.chain_step2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:49:53.500251+00:00
-- url     : https://prove2.me/submissions/e0d397bb-2c70-4808-a6f1-0a91bb5793fc

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
import Theorems.Thm_Comp_gStepF_eq

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution : chainGame.gStepF chainSafe chainSafe = chainR2 := by
  rw [gStepF_eq]; decide
end Comp
