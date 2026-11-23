-- Prove2me | solution 1 for Comp.chain_iter4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:51:15.156214+00:00
-- url     : https://prove2.me/submissions/a83cbcce-35b7-4692-900f-fc2bf2a549b7

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
import Theorems.Thm_Comp_chain_step1
import Theorems.Thm_Comp_chain_step2
import Theorems.Thm_Comp_chain_step3
import Theorems.Thm_Comp_chain_step4

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution : (chainGame.gStepF chainSafe)^[4] Finset.univ = chainGood := by
  have e4 : (4 : ℕ) = 3 + 1 := rfl
  have e3 : (3 : ℕ) = 2 + 1 := rfl
  have e2 : (2 : ℕ) = 1 + 1 := rfl
  rw [e4, Function.iterate_succ_apply, chain_step1, e3, Function.iterate_succ_apply, chain_step2,
    e2, Function.iterate_succ_apply, chain_step3, Function.iterate_one, chain_step4]
end Comp
