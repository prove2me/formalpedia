-- Prove2me | solution 1 for BKAR.Forest.activeExtension_singleton_order_mem_edgeSetOrders_of_support_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:16.115648+00:00
-- url     : https://prove2.me/submissions/0f6aa2cb-cd31-4aa5-b70f-298e907dae2b

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_activeExtension_forest_support_eq_singleton_empty
import Theorems.Thm_BKAR_ForestIndex_singleton_edges
import Theorems.Thm_BKAR_Forest_mem_edgeSetOrders_iff_toFinset_eq_and_nodup


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    {e : Edge V} (h : ActiveExtension (Forest.empty V) e)
    {I : ForestIndex V} (hsupport : h.forest.support = I) :
    [e] ∈ edgeSetOrders I.edges := by
  rw [mem_edgeSetOrders_iff_toFinset_eq_and_nodup]
  constructor
  · rw [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
    rw [← ForestIndex.singleton_edges e]
    rw [← activeExtension_forest_support_eq_singleton_empty h, hsupport]
  · exact List.nodup_singleton e
end BKAR.Forest
