-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.growth_branchPoint_of_initial_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:22.036854+00:00
-- url     : https://prove2.me/submissions/f0d1f398-b6af-4128-864f-76ac239e359b

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_Forest_ActiveExtension_consGrowth_branchPoint_of_initial_mem
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
    (u : F.EdgeParam → ℝ) (ts : List ℝ) {e' : Edge V}
    (he' : e' ∈ F.edges) :
    (data.growth e).branchPoint u ts e' = u ⟨e', he'⟩ :=
  (data.extension e).consGrowth_branchPoint_of_initial_mem
    (data.tail e) u ts he'
end BKAR.Forest.ActiveBranchData
