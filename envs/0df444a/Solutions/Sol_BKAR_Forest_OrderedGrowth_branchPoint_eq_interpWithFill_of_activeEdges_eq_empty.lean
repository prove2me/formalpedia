-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchPoint_eq_interpWithFill_of_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:38:05.201744+00:00
-- url     : https://prove2.me/submissions/ba7bd0c7-f46d-4793-8e81-fc993dd87e71

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_def
import Theorems.Thm_BKAR_Forest_interpWithFill_eq_standardInterp_of_activeEdges_eq_empty


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution
    (h : OrderedGrowth F order G) (u : F.EdgeParam → ℝ)
    (ts : List ℝ) (b : ℝ) (hG : G.activeEdges = ∅) :
    h.branchPoint u ts = G.interpWithFill (h.params u ts) b := by
  rw [branchPoint_def, G.interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
    (h.params u ts) b hG]
end BKAR.Forest.OrderedGrowth
