-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.derivativeOrder_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:18:06.987236+00:00
-- url     : https://prove2.me/submissions/70310bb2-8a61-4320-a4d3-515c358f2509

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G) :
    h.derivativeOrder = order.reverse :=
  rfl
end BKAR.Forest.OrderedGrowth
