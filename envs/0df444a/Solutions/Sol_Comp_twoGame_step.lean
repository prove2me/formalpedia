-- Prove2me | solution 1 for Comp.twoGame_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:40:28.463873+00:00
-- url     : https://prove2.me/submissions/50d30889-de70-4c68-b017-ef9d7b98e997

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_TwoStateQ
import Theorems.Thm_Comp_cert_true_v1
import Theorems.Thm_Comp_cert_false_v1
import Theorems.Thm_Comp_DiscountedCsgQ_shapley_eq_of_valueCert


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution : ∀ s, (twoGame.toDiscountedCSG twoGame_wf).shapley
    (fun s' => ((v1 s' : ℚ) : ℝ)) s = ((v2 s : ℚ) : ℝ) := by
  intro s
  cases s with
  | false => exact DiscountedCsgQ.shapley_eq_of_valueCert twoGame twoGame_wf cert_false_v1
  | true => exact DiscountedCsgQ.shapley_eq_of_valueCert twoGame twoGame_wf cert_true_v1
end Comp
