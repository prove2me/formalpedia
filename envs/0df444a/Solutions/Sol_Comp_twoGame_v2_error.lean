-- Prove2me | solution 1 for Comp.twoGame_v2_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:34:07.893381+00:00
-- url     : https://prove2.me/submissions/9ae85943-af71-4fc6-94f7-4aded8f839aa

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_TwoStateQ
import Theorems.Thm_Comp_twoGame_step
import Theorems.Thm_Comp_DiscountedCsgQ_two_dist_vOpt_lt_of_step


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution :
    2 * dist (fun s => ((v2 s : ℚ) : ℝ)) (twoGame.toDiscountedCSG twoGame_wf).vOpt
      < ((2 : ℚ) : ℝ) := by
  refine DiscountedCsgQ.two_dist_vOpt_lt_of_step twoGame twoGame_wf (d := 1 / 2) (by norm_num)
    (fun s => ?_) twoGame_step (by norm_num [twoGame])
  cases s <;> norm_num [v1, v2]
end Comp
