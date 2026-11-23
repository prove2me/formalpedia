-- Prove2me | solution 1 for Comp.stage_true_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:52:34.976071+00:00
-- url     : https://prove2.me/submissions/9a04bf56-5c27-4a76-8424-2e608c24ee60

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
    (twoGame.shapleyGameQ true v).A a1 a2 = 1 / 2 * (if a1 = a2 then v true else v false) := by
  cases a1 <;> cases a2 <;>
    simp [DiscountedCsgQ.shapleyGameQ, twoGame, twoK, twoR, CsgQ.expectQ, Fintype.sum_bool]
end Comp
