-- Prove2me | solution 1 for Evaluate.evaluate_evaluate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:58:29.800882+00:00
-- url     : https://prove2.me/submissions/c860fa1d-3af1-4f7f-a097-5793556cf3f8

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Evaluate
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_P2M_OBdd_evaluate_node___75814e9183f4
import Theorems.Thm_P2M_OBdd_evaluate_terminal__321343d95937
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Evaluate
namespace Evaluate
theorem _root_.solution : evaluate O = OBdd.evaluate O := by
  ext I
  unfold evaluate
  split
  next b hb => simp [OBdd.evaluate_terminal' hb]
  next j hj =>
    have := solution (O := O.low hj)
    have := solution (O := O.high hj)
    simp [OBdd.evaluate_node'' hj, *]
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
end Evaluate
