-- Prove2me | solution 1 for Csg.DiscountedCSG.shapley_aposteriori_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:32:51.905158+00:00
-- url     : https://prove2.me/submissions/19efa535-9704-48d1-988b-18b63ec51dfc

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
    dist (D.shapley^[n] v) D.vOpt ≤ dist (D.shapley^[n] v) (D.shapley^[n + 1] v) / (1 - D.lNN) :=
  D.contractingWith_shapley.aposteriori_dist_iterate_fixedPoint_le v n
end Csg.DiscountedCSG
