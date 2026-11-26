-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.first_mem_activeEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:14.949968+00:00
-- url     : https://prove2.me/submissions/9e0f9cf3-ec4a-40cb-8cb3-4dd983bb9f90

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
import Theorems.Thm_BKAR_Forest_ActiveExtension_mem_activeEdges
import Theorems.Thm_BKAR_Forest_EdgeExtension_mem_activeEdges


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F (e :: order) G) :
    e ∈ F.activeEdges :=
  h.firstActiveExtension.mem_activeEdges
end BKAR.Forest.OrderedGrowth
