-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.order_toFinset_card_eq_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:21.454658+00:00
-- url     : https://prove2.me/submissions/c9d46a33-658f-4509-9682-749bea8f7fc9

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_nodup

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G) :
    order.toFinset.card = order.length :=
  List.toFinset_card_of_nodup h.order_nodup
end BKAR.Forest.OrderedGrowth
