-- Prove2me | solution 1 for BKAR.Forest.activeExtension_forest_support_eq_singleton_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:06:05.294597+00:00
-- url     : https://prove2.me/submissions/6940645e-bcbc-4b12-bd57-bfd613c01817

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_ForestIndex_singleton_edges
import Theorems.Thm_BKAR_Forest_OrderedGrowth_support_edges
import Theorems.Thm_BKAR_Forest_TerminalGrowth_support_edges
import Theorems.Thm_BKAR_Forest_empty_edges
import Theorems.Thm_BKAR_Forest_support_edges


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    {e : Edge V} (h : ActiveExtension (Forest.empty V) e) :
    h.forest.support = ForestIndex.singleton e := by
  apply ForestIndex.ext
  rw [Forest.support_edges, ForestIndex.singleton_edges, h.extension.edges_eq,
    Forest.empty_edges]
  rfl
end BKAR.Forest
