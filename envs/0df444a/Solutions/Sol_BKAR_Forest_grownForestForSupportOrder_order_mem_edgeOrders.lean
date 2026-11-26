-- Prove2me | solution 1 for BKAR.Forest.grownForestForSupportOrder_order_mem_edgeOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:08.653531+00:00
-- url     : https://prove2.me/submissions/843b13eb-4470-4e6f-aa2e-5f6fc005f913

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_edges
import Theorems.Thm_BKAR_Forest_mem_edgeOrders_iff_toFinset_eq_and_nodup
import Theorems.Thm_BKAR_Forest_nodup_of_mem_edgeSetOrders
import Theorems.Thm_BKAR_Forest_toFinset_eq_of_mem_edgeSetOrders


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
    order.val ∈ (grownForestForSupportOrder choices I order).edgeOrders := by
  rw [mem_edgeOrders_iff_toFinset_eq_and_nodup]
  constructor
  · rw [toFinset_eq_of_mem_edgeSetOrders order.property,
      grownForestForSupportOrder_edges choices I order]
  · exact nodup_of_mem_edgeSetOrders order.property
end BKAR.Forest
