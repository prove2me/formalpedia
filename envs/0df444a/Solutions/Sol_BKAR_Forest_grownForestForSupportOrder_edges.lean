-- Prove2me | solution 1 for BKAR.Forest.grownForestForSupportOrder_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:56.711678+00:00
-- url     : https://prove2.me/submissions/ec281669-6735-4624-964c-95edcb865c4d

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_support
import Theorems.Thm_BKAR_Forest_OrderedGrowth_support_edges
import Theorems.Thm_BKAR_Forest_TerminalGrowth_support_edges
import Theorems.Thm_BKAR_Forest_support_edges


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges}) :
    (grownForestForSupportOrder choices I order).edges = I.edges := by
  rw [← Forest.support_edges (grownForestForSupportOrder choices I order)]
  exact congr_arg ForestIndex.edges
    (grownForestForSupportOrder_support choices I order)
end BKAR.Forest
