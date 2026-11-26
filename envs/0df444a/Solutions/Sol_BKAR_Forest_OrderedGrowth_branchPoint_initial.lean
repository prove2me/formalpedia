-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchPoint_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:37:34.96032+00:00
-- url     : https://prove2.me/submissions/e5573cb5-20c8-46b8-8002-0f8a87cf708e

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_def
import Theorems.Thm_BKAR_Forest_OrderedGrowth_initial_edges_subset_edges
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_initial
import Theorems.Thm_BKAR_Forest_standardInterp_of_mem


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) (e : F.EdgeParam) :
    h.branchPoint u ts e.val = u e := by
  rw [branchPoint_def]
  rw [G.standardInterp_of_mem (h.params u ts)
    (h.initial_edges_subset_edges e.property)]
  exact h.params_initial u ts e
end BKAR.Forest.OrderedGrowth
