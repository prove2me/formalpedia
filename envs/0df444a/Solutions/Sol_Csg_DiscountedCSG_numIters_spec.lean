-- Prove2me | solution 1 for Csg.DiscountedCSG.numIters_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:01:00.780365+00:00
-- url     : https://prove2.me/submissions/54785551-9e78-4fe1-b920-116055e9e45a

import Definitions.Def_Csg_Discounted
import Definitions.Def_Csg_DiscountedValueIteration

set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)
namespace Csg.DiscountedCSG
theorem _root_.solution {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) :
    D.stopCond eps v (D.numIters heps v) :=
  @Nat.find_spec _ (Classical.decPred _) (D.exists_stopCond heps v)
end Csg.DiscountedCSG
