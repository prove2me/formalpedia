-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchPoint_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:39:45.902222+00:00
-- url     : https://prove2.me/submissions/07c6053b-8376-40d1-9aad-bd5c2f06943b

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_mem_Icc_of_orderedSimplexParams
import Theorems.Thm_BKAR_Forest_standardInterp_mem_Icc


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) {top : ℝ} {ts : List ℝ}
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (htop : top ≤ 1) (hts : OrderedSimplexParams top ts)
    (e : Edge V) :
    0 ≤ h.branchPoint u ts e ∧ h.branchPoint u ts e ≤ 1 :=
  G.standardInterp_mem_Icc (h.params u ts)
    (h.params_mem_Icc_of_orderedSimplexParams u hu htop hts) e
end BKAR.Forest.OrderedGrowth
