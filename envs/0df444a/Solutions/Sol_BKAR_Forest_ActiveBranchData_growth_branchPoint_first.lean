-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.growth_branchPoint_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:20.145789+00:00
-- url     : https://prove2.me/submissions/13fa7917-0e0f-4784-a3e4-bc1c60fceaf1

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_Forest_ActiveExtension_consGrowth_branchPoint_first
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveBranchData
theorem _root_.solution (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (u : F.EdgeParam → ℝ) (t : ℝ) (ts : List ℝ) :
    (data.growth e).branchPoint u (t :: ts) e.val = t :=
  (data.extension e).consGrowth_branchPoint_first (data.tail e) u t ts
end BKAR.Forest.ActiveBranchData
