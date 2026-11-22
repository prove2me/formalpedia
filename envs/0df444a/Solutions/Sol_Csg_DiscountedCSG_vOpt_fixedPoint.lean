-- Prove2me | solution 1 for Csg.DiscountedCSG.vOpt_fixedPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:32:49.131844+00:00
-- url     : https://prove2.me/submissions/7a94ad97-8d76-4dec-b3cd-308daac7394d

import Definitions.Def_Csg_Discounted
import Definitions.Def_Csg_DiscountedValueIteration
import Theorems.Thm_Csg_DiscountedCSG_contractingWith_shapley


set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)
namespace Csg.DiscountedCSG
theorem _root_.solution : D.shapley D.vOpt = D.vOpt :=
  D.contractingWith_shapley.fixedPoint_isFixedPt
end Csg.DiscountedCSG
