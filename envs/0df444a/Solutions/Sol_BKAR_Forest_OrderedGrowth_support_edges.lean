-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.support_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:19.316257+00:00
-- url     : https://prove2.me/submissions/d22dada9-3e08-4ade-932c-45583585c610

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G) :
    h.support.edges = G.edges :=
  rfl
end BKAR.Forest.OrderedGrowth
