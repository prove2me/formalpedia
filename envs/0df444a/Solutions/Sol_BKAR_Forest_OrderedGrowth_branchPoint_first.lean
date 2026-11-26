-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchPoint_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:39:03.406366+00:00
-- url     : https://prove2.me/submissions/cdab3d2c-b3df-43ca-86f6-f6db3161039e

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_def
import Theorems.Thm_BKAR_Forest_OrderedGrowth_mem_edges_of_mem_order
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_first
import Theorems.Thm_BKAR_Forest_standardInterp_of_mem


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F (e :: order) G)
    (u : F.EdgeParam → ℝ) (t : ℝ) (ts : List ℝ) :
    h.branchPoint u (t :: ts) e = t := by
  rw [branchPoint_def]
  rw [G.standardInterp_of_mem (h.params u (t :: ts))
    (h.mem_edges_of_mem_order (by rw [List.mem_cons]; exact Or.inl rfl))]
  exact h.params_first u t ts
end BKAR.Forest.OrderedGrowth
