-- Prove2me | solution 1 for Evaluate.evaluate_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:09:03.049249+00:00
-- url     : https://prove2.me/submissions/fb1b6724-793f-4356-a79b-c411417901b3

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Evaluate
import Theorems.Thm_Evaluate_evaluate_evaluate
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_P2M_OBdd_evaluate_node___75814e9183f4
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Evaluate
namespace Evaluate
theorem _root_.solution {O : OBdd n m} (h : O.1.root = .node j) :
    evaluate O = fun I ↦ if I[O.1.heap[j].var] then evaluate (O.high h) I else evaluate (O.low h) I := by
  rw [evaluate_evaluate]
  rw [OBdd.evaluate_node'' h]
  simp [evaluate_evaluate]
end Evaluate
