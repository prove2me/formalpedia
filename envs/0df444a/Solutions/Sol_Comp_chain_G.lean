-- Prove2me | solution 1 for Comp.chain_G
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:52:37.666828+00:00
-- url     : https://prove2.me/submissions/d45f78a5-ebf2-41fd-a9f0-16d9973d1566

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
import Theorems.Thm_Comp_chain_fixed
import Theorems.Thm_Comp_chain_iter4
import Theorems.Thm_Comp_CsgQ_G_eq_coe_of_fixed


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution :
    (chainGame.toCSG chainGame_wf).G (↑chainSafe : Set Chain) = (↑chainGood : Set Chain) :=
  CsgQ.G_eq_coe_of_fixed chainGame chainGame_wf chainSafe chainGood 4 chain_iter4 chain_fixed
end Comp
