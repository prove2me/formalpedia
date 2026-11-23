-- Prove2me | solution 1 for Comp.twoGame_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:39:34.885534+00:00
-- url     : https://prove2.me/submissions/907c2a27-1289-4f68-90c7-b75853952f26

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_TwoStateQ
import Theorems.Thm_Comp_cert_true_star
import Theorems.Thm_Comp_cert_false_star
import Theorems.Thm_Comp_DiscountedCsgQ_shapley_eq_of_valueCert


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution : ∀ s, (twoGame.toDiscountedCSG twoGame_wf).shapley
    (fun s' => ((vStar s' : ℚ) : ℝ)) s = ((vStar s : ℚ) : ℝ) := by
  intro s
  cases s with
  | false => exact DiscountedCsgQ.shapley_eq_of_valueCert twoGame twoGame_wf cert_false_star
  | true => exact DiscountedCsgQ.shapley_eq_of_valueCert twoGame twoGame_wf cert_true_star
end Comp
