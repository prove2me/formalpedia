-- Prove2me | solution 1 for Csg.DiscountedCSG.shapley_apriori_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:24:28.449508+00:00
-- url     : https://prove2.me/submissions/3e66640c-fde6-4c73-92e1-36088f4503fb

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
theorem _root_.solution (v : S → ℝ) (n : ℕ) :
    dist (D.shapley^[n] v) D.vOpt ≤ dist v (D.shapley v) * (D.lNN : ℝ) ^ n / (1 - D.lNN) :=
  D.contractingWith_shapley.apriori_dist_iterate_fixedPoint_le v n
end Csg.DiscountedCSG
