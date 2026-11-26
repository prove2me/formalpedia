-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.first_not_mem_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:34:58.17446+00:00
-- url     : https://prove2.me/submissions/87fd0784-443d-4d74-9d73-261b73246032

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F (e :: order) G) :
    e ∉ F.edges :=
  h.firstStep.new_not_mem
end BKAR.Forest.OrderedGrowth
