-- Prove2me | solution 1 for Comp.DiscountedCsgQ.eq_vOpt_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:01:29.67813+00:00
-- url     : https://prove2.me/submissions/9c1a4fea-5cba-48f7-9b2b-8b36f6d61c75

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_DiscountedValueIteration
import Definitions.Def_Comp_Iterate
import Theorems.Thm_Csg_DiscountedCSG_contractingWith_shapley


set_option autoImplicit true
open Comp
open Csg
open Comp.DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace Comp.DiscountedCsgQ
theorem _root_.solution (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed) {v : S → ℚ}
    (hfix : ∀ s, (G.toDiscountedCSG h).shapley (fun s' => ((v s' : ℚ) : ℝ)) s
      = ((v s : ℚ) : ℝ)) :
    (fun s => ((v s : ℚ) : ℝ)) = (G.toDiscountedCSG h).vOpt :=
  (G.toDiscountedCSG h).contractingWith_shapley.fixedPoint_unique (funext hfix)
end Comp.DiscountedCsgQ
