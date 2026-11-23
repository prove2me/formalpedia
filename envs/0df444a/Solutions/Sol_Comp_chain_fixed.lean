-- Prove2me | solution 1 for Comp.chain_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:50:10.371506+00:00
-- url     : https://prove2.me/submissions/6025938b-4118-48d9-9ca6-bfae7465cc42

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
import Theorems.Thm_Comp_gStepF_eq

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution : chainGame.gStepF chainSafe chainGood = chainGood := by
  rw [gStepF_eq]; decide
end Comp
