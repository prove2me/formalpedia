-- Prove2me | solution 1 for Csg.DiscountedCSG.exists_unique_fixedPoint_choose_eq_vOpt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:24:18.262802+00:00
-- url     : https://prove2.me/submissions/22b3a861-cdea-44b8-a1b3-5fba6e7e6fbd

import Definitions.Def_Csg_Discounted
import Definitions.Def_Csg_DiscountedValueIteration
import Theorems.Thm_Csg_DiscountedCSG_contractingWith_shapley
import Theorems.Thm_Csg_DiscountedCSG_exists_unique_fixedPoint


set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)
namespace Csg.DiscountedCSG
theorem _root_.solution :
    D.exists_unique_fixedPoint.choose = D.vOpt :=
  D.contractingWith_shapley.fixedPoint_unique D.exists_unique_fixedPoint.choose_spec.1
end Csg.DiscountedCSG
