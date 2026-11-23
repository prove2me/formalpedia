-- Prove2me | solution 1 for Comp.chain_step1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:49:52.326268+00:00
-- url     : https://prove2.me/submissions/915c1ee9-4d81-41c5-9f14-3ead1bbdd3ef

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
import Theorems.Thm_Comp_gStepF_eq

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution : chainGame.gStepF chainSafe Finset.univ = chainSafe := by
  rw [gStepF_eq]; decide
end Comp
