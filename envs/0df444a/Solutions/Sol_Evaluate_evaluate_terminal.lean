-- Prove2me | solution 1 for Evaluate.evaluate_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:09:00.297519+00:00
-- url     : https://prove2.me/submissions/493b5a8b-adb9-4cb1-a846-974496a2d724

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Evaluate
import Theorems.Thm_Evaluate_evaluate_evaluate
import Theorems.Thm_P2M_OBdd_evaluate_terminal__321343d95937


set_option autoImplicit true
open Evaluate
namespace Evaluate
theorem _root_.solution {O : OBdd n m} : O.1.root = .terminal b → evaluate O = Function.const _ b := by
  rw [evaluate_evaluate]
  exact OBdd.evaluate_terminal'
end Evaluate
