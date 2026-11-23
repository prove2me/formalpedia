-- Prove2me | solution 1 for Comp.gStepF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:48:51.689153+00:00
-- url     : https://prove2.me/submissions/1314d2f5-0a76-4371-9397-98f6d5e0f723

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
import Theorems.Thm_Comp_pre1F_eq_pre1C

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution (x : Finset Chain) :
    chainGame.gStepF chainSafe x = pre1C x ∩ chainSafe := by
  unfold CsgQ.gStepF
  rw [pre1F_eq_pre1C]
end Comp
