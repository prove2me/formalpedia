-- Prove2me | solution 1 for BKAR.Forest.canonicalGrownForestForSupport_order_mem_edgeOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:49.30386+00:00
-- url     : https://prove2.me/submissions/c3cb7cb3-f73e-4b6c-b4de-14debc23d1b6

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_edges
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
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    {order : List (Edge V)} (horder : order ∈ edgeSetOrders I.edges) :
    order ∈ (canonicalGrownForestForSupport choices I).edgeOrders := by
  rw [mem_edgeOrders_iff_toFinset_eq_and_nodup]
  constructor
  · rw [toFinset_eq_of_mem_edgeSetOrders horder,
      canonicalGrownForestForSupport_edges choices I]
  · exact nodup_of_mem_edgeSetOrders horder
end BKAR.Forest
