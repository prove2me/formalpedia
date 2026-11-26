-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchPoint_mem_Icc_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:18:39.154811+00:00
-- url     : https://prove2.me/submissions/3cd71578-2531-429a-9f7f-124d4fe41d93

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_mem_Icc

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) {ts : List ℝ}
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (hts : OrderedSimplexParams 1 ts) (e : Edge V) :
    0 ≤ h.branchPoint u ts e ∧ h.branchPoint u ts e ≤ 1 :=
  h.branchPoint_mem_Icc u hu le_rfl hts e
end BKAR.Forest.OrderedGrowth
