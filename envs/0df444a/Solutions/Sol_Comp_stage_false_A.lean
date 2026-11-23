-- Prove2me | solution 1 for Comp.stage_false_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:52:48.942791+00:00
-- url     : https://prove2.me/submissions/0e52118e-33dc-4ce1-aad2-625878c3757c

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_TwoStateQ
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A



set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution (v : Bool → ℚ) (a1 a2 : Bool) :
    (twoGame.shapleyGameQ false v).A a1 a2 = 1 + 1 / 2 * v false := by
  simp [DiscountedCsgQ.shapleyGameQ, twoGame, twoK, twoR, CsgQ.expectQ, Fintype.sum_bool]
end Comp
