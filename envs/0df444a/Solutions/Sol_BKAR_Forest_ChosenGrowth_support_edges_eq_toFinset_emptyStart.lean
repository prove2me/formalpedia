-- Prove2me | solution 1 for BKAR.Forest.ChosenGrowth.support_edges_eq_toFinset_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:51:23.329801+00:00
-- url     : https://prove2.me/submissions/06cd3eab-118c-44bf-8a88-35407e586c40

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Theorems.Thm_BKAR_Forest_ChosenGrowth_edges_eq_toFinset_union
import Theorems.Thm_BKAR_Forest_OrderedGrowth_edges_eq_toFinset_union
import Theorems.Thm_BKAR_Forest_OrderedGrowth_support_edges
import Theorems.Thm_BKAR_Forest_TerminalGrowth_edges_eq_toFinset_union
import Theorems.Thm_BKAR_Forest_TerminalGrowth_support_edges
import Theorems.Thm_BKAR_Forest_empty_edges
import Theorems.Thm_BKAR_Forest_support_edges


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ChosenGrowth
variable {choices : ActiveExtensionChoice V}
variable {F G : Forest V} {order : List (Edge V)}
namespace BKAR.Forest.ChosenGrowth
theorem _root_.solution
    (path : ChosenGrowth choices (Forest.empty V) order G) :
    G.support.edges = order.toFinset := by
  rw [Forest.support_edges, path.edges_eq_toFinset_union, Forest.empty_edges,
    Finset.union_empty]
end BKAR.Forest.ChosenGrowth
