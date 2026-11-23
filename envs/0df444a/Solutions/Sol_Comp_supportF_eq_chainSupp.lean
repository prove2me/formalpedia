-- Prove2me | solution 1 for Comp.supportF_eq_chainSupp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:46:29.661674+00:00
-- url     : https://prove2.me/submissions/9a09b488-8e19-4d41-af99-c72fcb0fced7

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
import Theorems.Thm_Comp_supportF_dirac
import Theorems.Thm_Comp_supportF_coin

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution (s : Chain) (a1 a2 : Bool) :
    chainGame.supportF s a1 a2 = chainSupp s a1 a2 := by
  cases s <;> cases a1 <;> cases a2 <;>
    first
      | exact supportF_dirac rfl
      | exact supportF_coin rfl
end Comp
