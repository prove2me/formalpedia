-- Prove2me | solution 1 for Comp.twoGame_vOpt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:34:05.013796+00:00
-- url     : https://prove2.me/submissions/499835f9-210b-4d35-89ad-60c694d1abcc

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_TwoStateQ
import Theorems.Thm_Comp_twoGame_fixed
import Theorems.Thm_Comp_DiscountedCsgQ_eq_vOpt_of_fixed


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution :
    (fun s => ((vStar s : ℚ) : ℝ)) = (twoGame.toDiscountedCSG twoGame_wf).vOpt :=
  DiscountedCsgQ.eq_vOpt_of_fixed twoGame twoGame_wf twoGame_fixed
end Comp
